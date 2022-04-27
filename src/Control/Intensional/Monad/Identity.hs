{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Identity
( IntensionalIdentity(..)
) where

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Runtime

newtype IntensionalIdentity (c :: ConstraintFn) (a :: Type) =
  IntensionalIdentity a
  deriving (Eq, Ord, Show)

instance (Typeable c) => IntensionalFunctor (IntensionalIdentity c) where
  type IntensionalFunctorCF (IntensionalIdentity c) = c
  type IntensionalFunctorMapC (IntensionalIdentity c) a b =
    ()
  itsFmap = \%%c f (IntensionalIdentity a) -> IntensionalIdentity (f %@ a)

instance (Typeable c) => IntensionalApplicative (IntensionalIdentity c) where
  type IntensionalApplicativePureC (IntensionalIdentity c) a = (Typeable a)
  itsPure = \%c x -> IntensionalIdentity x
  type IntensionalApplicativeApC (IntensionalIdentity c) a b =
    (Typeable a, Typeable b)
  (%<*>) = \%%c (IntensionalIdentity f) (IntensionalIdentity a) ->
    IntensionalIdentity (f %@ a)

instance (Typeable c) => IntensionalMonad (IntensionalIdentity c) where
  type IntensionalMonadBindC (IntensionalIdentity c) a b =
    (Typeable a, Typeable b)
  itsBind = \%%c (IntensionalIdentity a) f -> f %@ a
