{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}
module Data.Tensor where

import Data.Kind
import Data.Functor.Identity
import Data.Bifunctor
import Data.Biapplicative

-------------------------------------------------------------------------------

type HKD ks = K ks -> Type

type Tensor' k = [k] -> k

newtype Tensor k = Tensor (Tensor' k)

-------------------------------------------------------------------------------

type        K :: [Type] -> Type
type family K ks = t | t -> ks where
  K '[]       = Type
  K (k ': ks) = k -> K ks

-----------------------------------------------------------------------------

type        Uncurry :: K ks -> HList Identity ks -> Type
data family Uncurry

data instance Uncurry (f :: K '[]) xs
  where
  Uncurry0 :: { curry0 :: f } -> Uncurry f 'HN

data instance Uncurry (f :: K '[x]) xs
  where
  Uncurry1 :: { curry1 :: f x } -> Uncurry f ('Identity x ':* 'HN)

data instance Uncurry (f :: K '[x, y]) xs
  where
  Uncurry2 :: { curry2 :: f x y } -> Uncurry f ('Identity x ':* 'Identity y ':* 'HN)

-------------------------------------------------------------------------------

infixr 4 :*
type HList :: (k -> Type) -> [k] -> Type
data HList f ts where
  HN :: HList f '[]
  (:*) :: f t -> HList f ts -> HList f (t ': ts)

type HSum :: (k -> Type) -> [k] -> Type
data HSum f ts where
  This  :: f t -> HSum f (t ': ts)
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

type Heads :: [HList Identity (x ': xs)] -> [x]
type family Heads ks where
  Heads '[] = '[]
  Heads (('Identity t ':* _) ': ks) = t ': Heads ks

type Tails :: [HList Identity (x ': xs)] -> [HList Identity xs]
type family Tails ks where
  Tails '[] = '[]
  Tails ((_ ':* ts) ': ks) = ts ': Tails ks

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

-------------------------------------------------------------------------------

type MonoidalN :: K ks -> ((HList Identity ks -> Type) -> [HList Identity ks] -> Type) -> HList Tensor ks -> Constraint
class MonoidalN (f :: K ks) output inputs | f -> output inputs
  where
  appendN :: output (Uncurry f) ts -> Uncurry f (Transpose inputs ts)

-------------------------------------------------------------------------------

instance MonoidalN (,) HList ('Tensor (HList Identity) ':* 'Tensor (HList Identity) ':* 'HN) where

  appendN HN = Uncurry2 $ (HN, HN)
  appendN (Uncurry2 f :* fs) = Uncurry2 $ biliftA2 (:*) (:*) (bimap Identity Identity f) (curry2 $ appendN fs)

-------------------------------------------------------------------------------

instance MonoidalN Maybe HList ('Tensor (HList Identity) ':* 'HN) where
  appendN HN = Uncurry1 $ Just HN
  appendN (Uncurry1 f :* fs) = Uncurry1 $ (:*) <$> (Identity <$> f) <*> (curry1 $ appendN fs)

-------------------------------------------------------------------------------

class HKDProduct (p :: HKD ks) where
  type HKDFields p :: [HList Identity ks]

  toHList   :: p f -> HList (Uncurry f) (HKDFields p)
  fromHList :: HList (Uncurry f) (HKDFields p) -> p f

-------------------------------------------------------------------------------

data Foo f = Foo
  { foo1 :: f Int
  }

instance HKDProduct Foo where
  type HKDFields Foo = '[ 'Identity Int ':* 'HN]

  toHList (Foo x) = Uncurry1 x :* HN
  fromHList (Uncurry1 x :* HN) = Foo x

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

  toHList (Bar x y) = Uncurry2 x :* Uncurry2 y :* HN
  fromHList (Uncurry2 x :* Uncurry2 y :* HN) = Bar x y

-------------------------------------------------------------------------------

-- type  HKDSum :: forall ks . HKD ks -> Constraint
-- class HKDSum s where
--   type HKDVariants s :: [HList Identity ks]

--   toHSum   :: s f -> HSum (Uncurry f) (HKDVariants s)
--   fromHSum :: HSum (Uncurry f) (HKDVariants s) -> s f
