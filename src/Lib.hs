{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}


module Lib where

import Data.Functor.Identity
import Unsafe.Coerce (unsafeCoerce)

----------
-- Comp --
----------

newtype Comp (f :: j -> *) (g :: i -> j) (a :: i) = Comp { getComp :: f (g a) }

----------------
-- Membership --
----------------

data Membership xs x where
  Here :: Membership (x ': ys) x
  There :: Membership ys x -> Membership (y ': ys) x

deriving instance Show (Membership xs x)

memToInt :: Membership xs x -> Int
memToInt Here = 0
memToInt (There mem) = 1 + memToInt mem

unsafeIntToMem :: Int -> Membership xs x
unsafeIntToMem 0 = unsafeCoerce Here
unsafeIntToMem n = unsafeCoerce $ There $ unsafeIntToMem (n - 1)

class Generate (xs :: [k]) where

  hgenerate
    :: forall f h
     . (Applicative f)
    => (forall x. Membership xs x -> f (h x))
    -> f (HList xs h)

instance Generate '[] where
  hgenerate
    :: forall f h
     . (Applicative f)
    => (forall x. Membership '[] x -> f (h x))
    -> f (HList '[] h)
  hgenerate _ = pure HNil

instance Generate ys => Generate (y ': ys) where
  hgenerate
    :: forall f h
     . Applicative f
    => (forall x. Membership (y ': ys) x -> f (h x))
    -> f (HList (y ': ys) h)
  hgenerate f =
    HCons <$> f Here <*> hgenerate (f . There)

hrepeat :: forall h xs. Generate xs => (forall x. Membership xs x -> h x) -> HList xs h
hrepeat f = runIdentity $ hgenerate (Identity . f)

-----------
-- HList --
-----------

data HList xs h where
  HNil :: HList '[] h
  HCons :: h x -> HList ys h -> HList (x ': ys) h

instance Show (HList '[] h) where
  show HNil = "HNil"

instance (Show (HList xs h), Show (h x)) => Show (HList (x ': xs) h) where
  show (HCons hx hlist) = "HCons (" <> show hx <> ") (" <> show hlist <> ")"

hlookup :: Membership xs x -> HList xs h -> h x
hlookup Here (HCons hx _) = hx
hlookup (There mem) (HCons _ rest) = hlookup mem rest

htraverse :: Applicative f => (forall x. g x -> f (h x)) -> HList xs g -> f (HList xs h)
htraverse _ HNil = pure HNil
htraverse f (HCons gx hlist) =
  let xxx = f gx
      yyy = htraverse f hlist
  in HCons <$> xxx <*> yyy

hmap :: (forall x. g x -> h x) -> HList xs g -> HList xs h
hmap _ HNil = HNil
hmap f (HCons gx hlist) = HCons (f gx) (hmap f hlist)

-- hmapWithIndex :: forall xs g h. (forall x. Membership xs x -> g x -> h x) -> HList xs g -> HList xs h
-- hmapWithIndex f = go 0
--   where
--     go :: forall ys. Int -> HList ys g -> HList ys h
--     go _ HNil = HNil
--     go n (HCons (gy :: g y) hlist) = HCons (f (unsafeIntToMem n :: Membership xs y) gy) (go (n + 1) hlist)

-- hmapWithIndex :: forall xs g h. (forall x. Membership xs x -> g x -> h x) -> HList xs g -> HList xs h
-- hmapWithIndex _ HNil = HNil
-- hmapWithIndex f hcons@(HCons _ _) = go 0 hcons
--   where
--     go :: forall y ys. Int -> HList (y ': ys) g -> HList (y ': ys) h
--     go n (HCons (gy :: g y) HNil) =
--       HCons
--         (f (unsafeIntToMem n :: Membership xs y) gy :: h y)
--         HNil
--     go n (HCons gy hlist@HCons{}) =
--       HCons
--         (f (unsafeIntToMem n :: Membership xs y) gy :: h y)
--         (go (n + 1) hlist :: HList ys h)

hmapWithIndex :: forall xs g h. (forall x. Membership xs x -> g x -> h x) -> HList xs g -> HList xs h
hmapWithIndex _ HNil = HNil
hmapWithIndex f hcons@(HCons _ _) = go Here hcons
  where
    go :: forall y ys. Membership xs y -> HList (y ': ys) g -> HList (y ': ys) h
    go mem (HCons (gy :: g y) HNil) =
      HCons
        (f mem gy :: h y)
        HNil
    go mem (HCons gy hlist@HCons{}) =
      HCons
        (f mem gy :: h y)
        (go (unsafeCoerce $ There mem) hlist :: HList ys h)

htraverseWithIndex
  :: forall xs g f h
   . Applicative f
  => (forall x. Membership xs x -> g x -> f (h x))
  -> HList xs g
  -> f (HList xs h)
htraverseWithIndex _ HNil = pure HNil
htraverseWithIndex f hcons@(HCons _ _) = go Here hcons
  where
    go :: forall y ys. Membership xs y -> HList (y ': ys) g -> f (HList (y ': ys) h)
    go mem (HCons (gy :: g y) HNil) =
      let xxx = f mem gy :: f (h y)
      in HCons <$> xxx <*> pure HNil
    go mem (HCons (gy :: g y) hlist@HCons{}) =
      let xxx = f mem gy :: f (h y)
          yyy = go (unsafeCoerce $ There mem) hlist :: f (HList ys h)
      in HCons <$> xxx <*> yyy

------------
-- Tangle --
------------

newtype Tangle xs h a = Tangle
  { unTangle :: HList xs (Comp (Tangle xs h) h) -> HList xs (Comp Maybe h) -> IO (a, HList xs (Comp Maybe h))
  }
  deriving Functor

instance Applicative (Tangle xs h) where
  pure a = Tangle $ \_ nulls -> pure (a, nulls)

  (<*>) :: Tangle xs h (a -> b) -> Tangle xs h a -> Tangle xs h b
  Tangle f <*> Tangle g = Tangle $ \r nulls -> do
    (a2b, nulls') <- f r nulls
    (a, nulls'') <- g r nulls'
    pure (a2b a, nulls'')

instance Monad (Tangle xs h) where
  (>>=) :: forall a b. Tangle xs h a -> (a -> Tangle xs h b) -> Tangle xs h b
  Tangle f >>= k = Tangle $ \r nulls -> do
    (a, nulls') <- f r nulls
    let Tangle g = k a :: Tangle xs h b
    (b, nulls'') <- g r nulls'
    pure (b, nulls'')

-- TODO: This doesn't use nulls
hitchAt :: Membership xs x -> Tangle xs h (h x)
hitchAt mem = Tangle $ \r nulls -> do
  let Tangle m = getComp $ hlookup mem r
  m r nulls

evalTangleT
  :: HList xs (Comp (Tangle xs h) h)
  -> HList xs (Comp Maybe h)
  -> Tangle xs h a
  -> IO a
evalTangleT tangles rec0 (Tangle m) = do
  (a, _nulls) <- m tangles rec0
  pure a

runTangles
  :: HList xs (Comp (Tangle xs h) h)
  -> HList xs (Comp Maybe h)
  -> IO (HList xs h)
runTangles tangles rec0 =
  evalTangleT tangles rec0 $
    htraverseWithIndex (\mem _ -> hitchAt mem) rec0

runTangles'
  :: HList xs (Comp (Tangle xs h) h)
  -> HList xs (Comp Maybe h)
  -> IO (HList xs h)
runTangles' tangles rec0 = do
  let Tangle m = htraverseWithIndex (\mem _ -> hitchAt mem) rec0
  (a, _nulls) <- m tangles rec0
  pure a


--------------------------------------------------------

example :: IO ()
example = do
  res <- runTangles
    (HCons x1 $ HCons x2 $ HCons x3 HNil)
    (HCons memo1 $ HCons memo2 $ HCons memo3 HNil)
  print (res :: HList '[Int, String, Double] Maybe)
  where
    x1 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe Int
    x1 = Comp $ pure (Just 3)

    x2 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe String
    x2 = Comp $ pure (Just "hello")

    x3 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe Double
    x3 = Comp $ pure Nothing

    memo1 :: Comp Maybe Maybe Int
    memo1 = Comp Nothing

    memo2 :: Comp Maybe Maybe String
    memo2 = Comp Nothing

    memo3 :: Comp Maybe Maybe Double
    memo3 = Comp Nothing

example2 :: IO ()
example2 = do
  res <- runTangles
    (hrepeat f)
    (hrepeat (\_mem -> Comp Nothing))
  print (res :: HList '[Int, String, Double] Maybe)
  where
    f
      :: Membership '[Int, String, Double] x
      -> Comp (Tangle '[Int, String, Double] Maybe) Maybe x
    f mem = Comp $ do
      something <- hitchAt mem
      pure something
