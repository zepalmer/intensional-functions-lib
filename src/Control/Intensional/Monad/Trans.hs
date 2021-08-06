{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Intensional.Monad.Trans
( IntensionalMonadTrans(..)
) where

import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Runtime

class IntensionalMonadTrans
    (t :: (Type -> Type) -> Type -> Type)
    where
  type IntensionalMonadTransLiftC t (m :: Type -> Type) a :: Constraint
  itsLift :: (IntensionalMonad m, IntensionalMonadTransLiftC t m a)
          => m a ->%(IntensionalFunctorCF m) t m a
