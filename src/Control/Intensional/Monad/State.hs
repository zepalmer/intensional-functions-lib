{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.State
( IntensionalState(..)
) where

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Runtime
import Control.Intensional.UtilityFunctions

newtype IntensionalState (c :: ConstraintFn) (s :: Type) (a :: Type) =
  IntensionalState (s ->%c (s, a))

instance (Typeable c, Typeable s)
    => IntensionalFunctor (IntensionalState c s) where
  type IntensionalFunctorCF (IntensionalState c s) = c
  type IntensionalFunctorMapC (IntensionalState c s) a b =
      ( Typeable a, Typeable b
      , c (s ->%c (s,a))
      , c ((s, a) ->%c (s,b))
      , c (a ->%c b)
      )
  itsFmap = \%%c mapper (IntensionalState f) ->
      IntensionalState (itsCompose @c %@% (itsSecond @c %@ mapper, f))

instance (Typeable c, Typeable s)
    => IntensionalApplicative (IntensionalState c s) where
  type IntensionalApplicativePureC (IntensionalState c s) a =
    ( Typeable a, c a )
  type IntensionalApplicativeApC (IntensionalState c s) a b =
    ( Typeable a, Typeable b
    , c (s ->%c (s, a ->%c b))
    , c (s ->%c (s, a))
    )
  itsPure = \%c x -> IntensionalState (\%c s -> (s, x))
  (%<*>) = \%%c (IntensionalState fnS) (IntensionalState xS) ->
    IntensionalState $
      \%c s ->
        let (s', x) = xS %@ s in
        let (s'', fn) = fnS %@ s' in
        (s'', fn %@ x)

instance (Typeable c, Typeable s)
    => IntensionalMonad (IntensionalState c s) where
  type IntensionalMonadBindC (IntensionalState c s) a b =
    ( Typeable a, Typeable b
    , c (a ->%c IntensionalState c s b)
    , c (s ->%c (s, a))
    )
  itsBind = \%%c (IntensionalState xS) f ->
    IntensionalState $
      \%c s ->
        let (s', x) = xS %@ s in
        let (IntensionalState bS) = f %@ x in
        bS %@ s'