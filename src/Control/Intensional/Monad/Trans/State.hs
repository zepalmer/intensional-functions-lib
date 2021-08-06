{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.State
( StateT(..)
, evalStateT
) where

-- | An intensional analogue to Control.Monad.Trans.State.

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Monad.Trans
import Control.Intensional.Runtime

newtype StateT (c :: ConstraintFn) s (m :: Type -> Type) a =
  StateT { runStateT :: s ->%c m (a,s) }

deriving instance
     (Eq (s ->%c (m (a,s))))
  => (Eq (StateT c s m a))
deriving instance
     (Ord (s ->%c (m (a,s))))
  => (Ord (StateT c s m a))

evalStateT :: forall c s m a.
              ( IntensionalMonad m
              , IntensionalApplicativePureC m a
              , IntensionalMonadBindC m (a,s) a
              , c ~ IntensionalFunctorCF m
              , Typeable s, Typeable a
              , c (HList '[StateT c s m a])
              )
           => StateT c s m a ->%c s ->%c m a
evalStateT = \%c m s ->
  intensional c do
    ~(a, _) <- runStateT m %@ s
    itsPure %@ a

instance IntensionalMonadTrans (StateT c s) where
  type IntensionalMonadTransLiftC (StateT c s) m a =
    ( c ~ IntensionalFunctorCF m
    , Typeable s, Typeable a
    , c (HList '[m a])
    , c (HList '[s])
    , IntensionalApplicativePureC m (a,s)
    , IntensionalMonadBindC m a (a,s)
    )
  itsLift = \%c m ->
    StateT $ \%c s -> intensional c do
      a <- m
      itsPure %@ (a, s)
