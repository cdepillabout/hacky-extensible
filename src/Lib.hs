{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}


module Lib where

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

-----------
-- HList --
-----------

data HList xs h where
  HNil :: HList '[] h
  HCons :: h x -> HList xs h -> HList (x ': xs) h

hlookup :: Membership xs x -> HList xs h -> h x
hlookup Here (HCons hx _) = hx
hlookup (There mem) (HCons _ rest) = hlookup mem rest

htraverse :: Applicative f => (forall x. g x -> f (h x)) -> HList xs g -> f (HList xs h)
htraverse f hlist = _

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

-- runTangles
--   :: HList xs (Comp (Tangle xs h) h)
--   -> HList xs (Comp Maybe h)
--   -> IO (HList xs h)
-- runTangles tangles rec0 =
--   evalTangleT tangles rec0 $
--     Tangle $ \r null -> do
--       -- r :: HList xs (Comp (Tangle xs h) h)
--       pure (_ :: HList xs h, null)
