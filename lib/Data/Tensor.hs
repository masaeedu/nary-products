{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DerivingStrategies       #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies   #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE LambdaCase               #-}
module Data.Tensor where

import Data.Kind
import Data.Functor.Identity
import Data.Bifunctor
import Data.Biapplicative
import Control.Category

-------------------------------------------------------------------------------
type HKD ks = K ks -> Type

type    Tensor' k = [k] -> k
newtype Tensor  k = Tensor (Tensor' k)

type    Arrow' k = k -> k -> Type
newtype Arrow  k = Arrow (Arrow' k)

-- type AllArrows :: ()
-- type family AllArrows c as where
--   AllArrows _ 'HN = ()
--   AllArrows c ('Arrow a ':* as) = (c a, AllArrows c as)

-------------------------------------------------------------------------------
type        K :: [Type] -> Type
type family K ks = t | t -> ks where
  K '[]       = Type
  K (k ': ks) = k -> K ks

-----------------------------------------------------------------------------
type        Curried ::  K ks -> HList Identity ks -> Type
type family Curried f ts where
  Curried @'[]       f _  = f
  Curried @(k ': ks) f ts = Curried (f (Head ts)) (Tail ts)

newtype Uncurry f ts = Uncurry{ curry' :: Curried f ts }

deriving stock instance Show (Curried f ts) => Show (Uncurry f ts)

-------------------------------------------------------------------------------
type AllF :: (k -> Constraint) -> (l -> k) -> [l] -> Constraint
type family AllF c f ts where
  AllF _ _ '[]       = ()
  AllF c f (t ': ts) = (c (f t), AllF c f ts)

-------------------------------------------------------------------------------
infixr 4 :*
type HList :: (k -> Type) -> [k] -> Type
data HList f ts where
  HN :: HList f '[]
  (:*) :: f t -> HList f ts -> HList f (t ': ts)

deriving stock instance AllF Show f ts => Show (HList f ts)

type HSum :: (k -> Type) -> [k] -> Type
data HSum f ts where
  Here  :: f t -> HSum f (t ': ts)
  There :: HSum f ts -> HSum f (t ': ts)

-------------------------------------------------------------------------------
type Transpose
  :: HList Tensor ks
  -> [HList Identity ks]
  -> HList Identity ks
type Transpose (ts :: HList Tensor ks) xss = ZipWithTensor ts (SequenceHList ks xss)

type SequenceHList
  :: forall ks
  -> [HList Identity ks]
  -> HList [] ks
type family SequenceHList ks tss where
  SequenceHList '[]       _   = 'HN
  SequenceHList (k ': ks) tss = Heads tss ':* SequenceHList ks (Tails tss)

type Heads :: [HList Identity (k ': ks)] -> [k]
type family Heads ts where
  Heads '[] = '[]
  Heads (t ': ts) = Head t ': Heads ts

type Head :: HList Identity (k ': ks) -> k
type family Head ts = t where
  Head ('Identity t ':* _) = t

type Tails :: [HList Identity (k ': ks)] -> [HList Identity ks]
type family Tails ts where
  Tails '[] = '[]
  Tails (t ': ts) = Tail t ': Tails ts

type Tail :: HList Identity (k ': ks) -> HList Identity ks
type family Tail ts where
  Tail (_ ':* ts) = ts

-- | Can't actually use this because Haskell sucks, have to defunctionalize
-- type ZipWithH
--   :: (forall x. f x -> g x -> h x)
--   -> HList f xs
--   -> HList g xs
--   -> HList h xs
-- type family ZipWithH k xs ys where
--   ZipWithH k 'HN 'HN = 'HN
--   ZipWithH k (x ':* xs) (y ':* ys) = k x y ':* ZipWithH k xs ys

type ZipWithTensor
  :: HList Tensor xs
  -> HList []       xs
  -> HList Identity xs
type family ZipWithTensor ts xsx where
  ZipWithTensor 'HN 'HN = 'HN
  ZipWithTensor ('Tensor t ':* ts) (xs ':* xss) =
    'Identity (t xs) ':* ZipWithTensor ts xss

type ZipWithCons
  :: HList Identity xs
  -> HList []       xs
  -> HList []       xs
type family ZipWithCons xs ys where
  ZipWithCons 'HN                  'HN          =
    'HN
  ZipWithCons ('Identity x ':* xs) (ys ':* yss) =
    (x ': ys) ':* ZipWithCons xs yss

type ZipWithHList
  :: HList Identity xs
  -> HList Identity ys
  -> HList (HList Identity) (ZipWithList xs ys)
type family ZipWithHList xs ys where
  ZipWithHList 'HN                  'HN          =
    'HN
  ZipWithHList ('Identity x ':* xs) ('Identity y ':* ys) =
    ('Identity x ':* 'Identity y ':* 'HN) ':* ZipWithHList xs ys

type ZipWithList :: [x] -> [x] -> [[x]]
type family ZipWithList xs ys where
  ZipWithList '[] '[] = '[]
  ZipWithList (x ': xs) (y ': ys) = '[x, y] ': ZipWithList xs ys

type ZipArrowsWithArgs
  :: HList Arrow    ks
  -> HList Identity ks
  -> HList Identity ks
  -> [Type]
type family ZipArrowsWithArgs as xs ys = t | t -> as where
  ZipArrowsWithArgs @'[] 'HN _ _ = '[]
  ZipArrowsWithArgs @(_ ': _) ('Arrow    a ':* as) xs ys =
    a (Head xs) (Head ys) ': ZipArrowsWithArgs as (Tail xs) (Tail ys)

-------------------------------------------------------------------------------
class FunctorN (f :: K ks)
  where
  type FieldArrows f :: HList Arrow ks

  mapN
    :: HList Identity (ZipArrowsWithArgs (FieldArrows f) ts ss)
    -> Uncurry f ts -> Uncurry f ss

instance FunctorN (,)
  where
  type FieldArrows (,) = 'Arrow (->) ':* 'Arrow (->) ':* 'HN
  mapN (Identity f :* Identity g :* HN) (Uncurry t) = Uncurry $ bimap f g t

class MonoidalN (f :: K ks)
  where
  type InputTensor  f :: (HList Identity ks -> Type) -> [HList Identity ks] -> Type
  type InputTensor  f = HList
  type FieldTensors f :: HList Tensor ks

  appendN :: (InputTensor f) (Uncurry f) ts -> Uncurry f (Transpose (FieldTensors f) ts)

-------------------------------------------------------------------------------
instance MonoidalN (,) where
  type FieldTensors (,) = 'Tensor (HList Identity) ':* 'Tensor (HList Identity) ':* 'HN

  appendN HN = Uncurry $ (HN, HN)
  appendN (Uncurry f :* fs) = Uncurry $ biliftA2 (:*) (:*) (bimap Identity Identity f) (curry' $ appendN fs)

-------------------------------------------------------------------------------
instance MonoidalN Maybe where
  type FieldTensors Maybe = 'Tensor (HList Identity) ':* 'HN

  appendN HN = Uncurry $ Just HN
  appendN (Uncurry f :* fs) = Uncurry $ (:*) <$> (Identity <$> f) <*> (curry' $ appendN fs)

-------------------------------------------------------------------------------
class HKDProduct (p :: HKD ks) where
  type HKDFields p :: [HList Identity ks]

  toHList   :: p f -> HList (Uncurry f) (HKDFields p)
  fromHList :: HList (Uncurry f) (HKDFields p) -> p f

-------------------------------------------------------------------------------
data Foo f = Foo
  { foo1 :: f Int
  }

deriving stock instance (forall a . Show (f a)) => Show (Foo f)

instance HKDProduct Foo where
  type HKDFields Foo = '[ 'Identity Int ':* 'HN]

  toHList (Foo x) = Uncurry x :* HN
  fromHList (Uncurry x :* HN) = Foo x

-------------------------------------------------------------------------------
data Bar f = Bar
  { bar1 :: f "a" String
  , bar2 :: f "b" Char
  }

instance HKDProduct Bar where
  type HKDFields Bar = '[
      'Identity "a" ':* 'Identity String ':* 'HN
    , 'Identity "b" ':* 'Identity Char ':* 'HN
    ]

  toHList (Bar x y) = Uncurry x :* Uncurry y :* HN
  fromHList (Uncurry x :* Uncurry y :* HN) = Bar x y

-------------------------------------------------------------------------------
type  HKDSum :: forall ks . HKD ks -> Constraint
class HKDSum s where
  type HKDVariants s :: [HList Identity ks]

  toHSum   :: s f -> HSum (Uncurry f) (HKDVariants s)
  fromHSum :: HSum (Uncurry f) (HKDVariants s) -> s f

-------------------------------------------------------------------------------
data Baz f = Baz1 (f Int) | Baz2 (f Char)

instance HKDSum Baz where
  type HKDVariants Baz = '[ 'Identity Int ':* 'HN, 'Identity Char ':* 'HN]

  toHSum = \case
    Baz1 fi -> Here (Uncurry fi)
    Baz2 fc -> There (Here (Uncurry fc))
  fromHSum = \case
    Here (Uncurry fi) -> Baz1 fi
    There (Here (Uncurry fc)) -> Baz2 fc


data Bots b = Bots{
    foo :: b Int Char
  , bar :: b String Float
  }
