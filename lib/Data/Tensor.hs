{-# LANGUAGE TypeFamilyDependencies #-}
module Data.Tensor where

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Identity
import GHC.TypeLits
import Data.Proxy
import Data.Functor.Const
import Data.Bifunctor
import Data.Biapplicative

-------------------------------------------------------------------------------
type HKD ks = K ks -> Type

-------------------------------------------------------------------------------
type        TensorsOf :: [Type] -> [Type]
type family TensorsOf ts = r | r -> ts where
  TensorsOf '[] = '[]
  TensorsOf (t ': ts) = ([t] -> t) ': TensorsOf ts

-------------------------------------------------------------------------------
type        K :: [Type] -> Type
type family K ks = t | t -> ks where
  K '[]       = Type
  K (k ': ks) = k -> K ks

-----------------------------------------------------------------------------

type Uncurry :: K ks -> HList Identity ks -> Type
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
data HList f ts where
  HN :: HList f '[]
  (:*) :: f t -> HList f ts -> HList f (t ': ts)

data HSum f ts where
  This  :: f t -> HSum f (t ': ts)
  There :: HSum f ts -> HSum f (t ': ts)

-------------------------------------------------------------------------------
type AppendN
  :: HList TensorOf ks
  -> [HList Identity ks]
  -> HList Identity ks
type AppendN (ts :: HList TensorOf ks) xss = ZipWithTensor ts (SequenceHList ks xss)

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

-- type ZipWithH
--   :: (forall x . f x -> g x -> h x)
--   -> HList f xs
--   -> HList g xs
--   -> HList h xs
-- type family ZipWithH f xs ys where
--   ZipWithH f 'HN 'HN = 'HN
--   ZipWithH f (x ':* xs) (y ':* ys) = f x y ':* ZipWithH f xs ys

type ZipWithTensor
  :: HList TensorOf xs
  -> HList []       xs
  -> HList Identity xs
type family ZipWithTensor ts xsx where
  ZipWithTensor 'HN 'HN = 'HN
  ZipWithTensor ('TensorOf t ':* ts) (xs ':* xss) =
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

-- SequenceHList [H.[Maybe,Int], H.[IO,()]] = H.[[Maybe,IO], [Int,()]]

-------------------------------------------------------------------------------

-- ks           =       [Type -> Type, Type          ]
-- ts           = HList.[[]          , Int           ]
-- TensorsOf ks = HList.[ComposeN    , HList Identity]
-- _ :: HList Identity ks

-- class SequenceHList tss where
--   type ResultIndices tss :: 
--   type Result        tss :: HList Identity (ResultIndices tss)
--   sequenceHList :: HList ((:$:) f) tss
--                 -> f :$: (HList (HList Identity (Map First)))

-- instance SequenceHList 'HN where

-- class SequenceHList tss where
--   sequenceHList :: MonoidalInAll f => HList f [[a, b, c], [d, e, f]] -> f [a, d] [b, e] [c, f]
 
newtype TensorOf k = TensorOf ([k] -> k)

class MonoidalN (f :: K ks) where
  type FieldTensors f :: HList TensorOf ks

  appendN :: forall (ts :: [HList Identity ks]) . HList (Uncurry f) ts -> Uncurry f (AppendN (FieldTensors f) ts)

instance MonoidalN (,) where
  type FieldTensors (,) =
    'TensorOf (HList Identity) ':* 'TensorOf (HList Identity) ':* 'HN

  appendN HN = Uncurry2 $ (HN, HN)
  appendN (Uncurry2 f :* fs) = Uncurry2 $ biliftA2 (:*) (:*) (bimap Identity Identity f) (curry2 $ appendN fs)

instance MonoidalN Maybe where
  type FieldTensors Maybe = 'TensorOf (HList Identity) ':* 'HN

  appendN HN = Uncurry1 $ Just HN
  appendN (Uncurry1 f :* fs) = Uncurry1 $ (:*) <$> (Identity <$> f) <*> (curry1 $ appendN fs)

-------------------------------------------------------------------------------
class HKDProduct (p :: HKD ks) where
  type HKDFields p :: [HList Identity ks]

  toHList   :: p f -> HList (Uncurry f) (HKDFields p)
  fromHList :: HList (Uncurry f) (HKDFields p) -> p f

-------------------------------------------------------------------------------
data Foo f = Foo (f Int)

instance HKDProduct Foo where
  type HKDFields Foo = '[ 'Identity Int ':* 'HN]

  toHList (Foo x) = Uncurry1 x :* HN
  fromHList (Uncurry1 x :* HN) = Foo x

-------------------------------------------------------------------------------
data Foo' f = Foo' (f "a" String) (f "b" Char)

instance HKDProduct Foo' where
  type HKDFields Foo' = '[
      'Identity "a" ':* 'Identity String ':* 'HN
    , 'Identity "b" ':* 'Identity Char ':* 'HN
    ]

  toHList (Foo' x y) = Uncurry2 x :* Uncurry2 y :* HN
  fromHList (Uncurry2 x :* Uncurry2 y :* HN) = Foo' x y

-------------------------------------------------------------------------------
-- type  HKDSum :: forall ks . HKD ks -> Constraint
-- class HKDSum s where
--   type HKDVariants s :: [HList Identity ks]

--   toHSum   :: s f -> HSum (Uncurry f) (HKDVariants s)
--   fromHSum :: HSum (Uncurry f) (HKDVariants s) -> s f
