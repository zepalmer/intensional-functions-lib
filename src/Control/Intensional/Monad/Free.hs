{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Intensional.Monad.Free (
  FreeIntensionalMonad(..),
  --fimForget,
  --fimInterpret,
) where

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Runtime

{- ========== Free Intensional Monad ========== -}

data FreeIntensionalMonad
        (c :: ConstraintFn)
        (m :: Type -> Type)
        (a :: Type)
    where
  FimPure :: a
          -> FreeIntensionalMonad c m a
  FimFmap :: (a ->%c b)
          -> FreeIntensionalMonad c m a
          -> FreeIntensionalMonad c m b
  FimAp :: FreeIntensionalMonad c m (a ->%c b)
        -> FreeIntensionalMonad c m a
        -> FreeIntensionalMonad c m b
  FimBind :: FreeIntensionalMonad c m a
          -> (a ->%c FreeIntensionalMonad c m b)
          -> FreeIntensionalMonad c m b
  deriving (Typeable)

{- ========== Free Intensional Monad Instances ========== -}

instance (Typeable c, Typeable m)
    => IntensionalFunctor (FreeIntensionalMonad c m) where
  type IntensionalFunctorCF (FreeIntensionalMonad c m) = c
  type IntensionalFunctorMapC (FreeIntensionalMonad c m) a b =
    ()
  itsFmap = \%%c f a -> FimFmap f a

instance (Typeable c, Typeable m)
    => IntensionalApplicative (FreeIntensionalMonad c m) where
  type IntensionalApplicativePureC (FreeIntensionalMonad c m) a =
    (Typeable a)
  type IntensionalApplicativeApC (FreeIntensionalMonad c m) a b =
    (Typeable a, Typeable b)
  itsPure = \%c x -> FimPure x
  (%<*>) = \%%c f a -> FimAp f a

instance (Typeable c, Typeable m)
    => IntensionalMonad (FreeIntensionalMonad c m) where
  type IntensionalMonadBindC (FreeIntensionalMonad c m) a b =
    (Typeable a, Typeable b)
  itsBind = \%%c a f -> FimBind a f
