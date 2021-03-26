{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


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

------------
-- Tangle --
------------

newtype Tangle xs h a = Tangle
  { unTangle :: (HList xs (Comp (Tangle xs h) h)) -> (HList xs (Comp Maybe h)) -> IO (a, HList xs (Comp Maybe h))
  }

hitchAt :: Membership xs x -> Tangle xs h (h x)
hitchAt k = undefined

evalTangleT
  :: HList xs (Comp (Tangle xs h) h)
  -> HList xs (Comp Maybe h)
  -> Tangle xs h a
  -> IO a
evalTangleT tangles rec0 (Tangle m) = undefined

runTangles
  :: HList xs (Comp (Tangle xs h) h)
  -> HList xs (Comp Maybe h)
  -> IO (HList xs h)
runTangles = undefined
