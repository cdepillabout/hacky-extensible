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

import Control.Monad.IO.Class
import Data.Functor.Identity
-- import Data.Typeable
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
  { unTangle :: HList xs (Comp (Tangle xs h) h) -> IO a
  }
  deriving Functor

instance Applicative (Tangle xs h) where
  pure a = Tangle $ \_ -> pure a

  (<*>) :: Tangle xs h (a -> b) -> Tangle xs h a -> Tangle xs h b
  Tangle f <*> Tangle g = Tangle $ \r -> do
    a2b <- f r
    a <- g r
    pure $ a2b a

instance Monad (Tangle xs h) where
  (>>=) :: forall a b. Tangle xs h a -> (a -> Tangle xs h b) -> Tangle xs h b
  Tangle f >>= k = Tangle $ \r -> do
    a <- f r
    let Tangle g = k a :: Tangle xs h b
    b <- g r
    pure b

instance MonadFail (Tangle xs h) where
  fail str = Tangle $ \_ -> fail str

instance MonadIO (Tangle xs h) where
  liftIO f = Tangle $ \_ -> do
    res <- f
    pure res

-- TODO: This doesn't use nulls
hitchAt :: Membership xs x -> Tangle xs h (h x)
hitchAt mem = Tangle $ \r -> do
  let Tangle m = getComp $ hlookup mem r
  m r

evalTangleT
  :: HList xs (Comp (Tangle xs h) h)
  -> Tangle xs h a
  -> IO a
evalTangleT tangles (Tangle m) = do
  a <- m tangles
  pure a

runTangles
  :: HList xs (Comp (Tangle xs h) h)
  -> IO (HList xs h)
runTangles tangles =
  evalTangleT tangles $
    htraverseWithIndex (\mem _ -> hitchAt mem) tangles

runTangles'
  :: forall xs h
   . HList xs (Comp (Tangle xs h) h)
  -> IO (HList xs h)
runTangles' tangles = do
  let tangle = htraverseWithIndex f tangles :: Tangle xs h (HList xs h)
      m = unTangle tangle
          :: HList xs (Comp (Tangle xs h) h)
          -> IO (HList xs h)
  a <- m tangles
  pure a
  where
    f :: forall x b. Membership xs x -> b -> Tangle xs h (h x)
    f mem _ = Tangle $ \(r :: HList xs (Comp (Tangle xs h) h)) -> do
      let comp = hlookup mem r :: Comp (Tangle xs h) h x
          tangle = getComp comp :: Tangle xs h (h x)
          n = unTangle tangle :: HList xs (Comp (Tangle xs h) h) -> IO (h x)
      n r

runTangles''
  :: forall xs h
   . HList xs (Comp (Tangle xs h) h)
  -> IO (HList xs h)
runTangles'' tangles = do
  let tangle = hlistToGenerate tangles $ hgenerate f :: Tangle xs h (HList xs h)
      m = unTangle tangle :: HList xs (Comp (Tangle xs h) h) -> IO (HList xs h)
  a <- m tangles :: IO (HList xs h)
  pure a
  where
    f :: forall x. Membership xs x -> Tangle xs h (h x)
    f mem = Tangle $ go mem

    go :: forall x. Membership xs x -> HList xs (Comp (Tangle xs h) h) -> IO (h x)
    go mem r = do
      let comp = hlookup mem r :: Comp (Tangle xs h) h x
          tangle = getComp comp :: Tangle xs h (h x)
          n = unTangle tangle :: HList xs (Comp (Tangle xs h) h) -> IO (h x)
      putStrLn $ "In runTangles'', f, before running inner action n for membership " <> show (memToInt mem)
      sss <- n r :: IO (h x)
      putStrLn $ "In runTangles'', f, after running inner action n for membership " <> show (memToInt mem)
      pure sss

hlistToGenerate :: HList xs h -> (Generate xs => r) -> r
hlistToGenerate HNil r = r
hlistToGenerate (HCons _ inner) r = hlistToGenerate inner r

--------------------------------------------------------

example :: IO ()
example = do
  res <- runTangles''
    (HCons x1 $ HCons x2 $ HCons x3 HNil)
  print (res :: HList '[Int, String, Double] Maybe)
  where
    x1 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe Int
    x1 = Comp xxx1

    xxx1 :: Tangle '[Int, String, Double] Maybe (Maybe Int)
    xxx1 =
      Tangle $
        \(r :: HList
                '[Int, String, Double]
                (Comp (Tangle '[Int, String, Double] Maybe) Maybe)
         ) -> do
            putStrLn "Evaluating x1, String, about to pull out x2"
            let mem = There Here :: Membership '[Int, String, Double] String
                rrr = hlookup mem r :: Comp (Tangle '[Int, String, Double] Maybe) Maybe String
                bbb = getComp rrr :: Tangle '[Int, String, Double] Maybe (Maybe String)
                ggg = unTangle bbb :: HList '[Int, String, Double] (Comp (Tangle '[Int, String, Double] Maybe) Maybe) -> IO (Maybe String)
            Just str <- ggg r :: IO (Maybe String)
            putStrLn "Evaluating x1, finished pulling out x2"
            pure $ Just $ read str

    x2 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe String
    x2 = Comp $ do
      liftIO $ putStrLn "Evaluating x2, String"
      pure (Just "100")

    x3 :: Comp (Tangle '[Int, String, Double] Maybe) Maybe Double
    x3 = Comp $ pure Nothing

example2 :: IO ()
example2 = do
  res <- runTangles (hrepeat f)
  print (res :: HList '[Int, String, Double] Maybe)
  where
    f
      :: {- Typeable x
      => -} Membership '[Int, String, Double] x
      -> Comp (Tangle '[Int, String, Double] Maybe) Maybe x
    f Here = Comp $ do
      maybeStr <- hitchAt (There Here)
      pure (fmap read maybeStr)
    f (There Here) = Comp $ do
      pure (Just "100")
    f _ = Comp $ do
      pure Nothing
