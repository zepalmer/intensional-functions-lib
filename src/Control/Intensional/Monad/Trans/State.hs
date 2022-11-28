{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.State
( StateT(..)
, evalStateT
, itsGet
, itsSet
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
              ( Typeable a
              , Typeable c
              , Typeable m
              , Typeable s
              , c ~ IntensionalFunctorCF m
              , c (StateT c s m a)
              , IntensionalMonad m
              , IntensionalApplicativePureC m a
              , IntensionalMonadBindC m (a, s) a
              )
           => StateT c s m a ->%c s ->%c m a
evalStateT = \%c m s ->
  intensional c do
    ~(a, _) <- runStateT m %@ s
    itsPure %@ a

instance ( Typeable c
         , Typeable s
         , Typeable m
         , c ~ IntensionalFunctorCF m
         , IntensionalMonad m
         )
      => IntensionalFunctor (StateT c s m) where
  type IntensionalFunctorCF (StateT c s m) = c
  type IntensionalFunctorMapC (StateT c s m) a b =
      ( Typeable a
      , Typeable b
      , c (a ->%c b)
      , c (s ->%c m (a,s))
      , IntensionalApplicativePureC m (b,s)
      , IntensionalMonadBindC m (a,s) (b,s)
      )
  itsFmap = \%%c ab (StateT sma) ->
    StateT $ \%c s ->
      intensional c do
        (a,s') <- sma %@ s
        itsPure %@ (ab %@ a, s')

instance ( Typeable c
         , Typeable m
         , Typeable s
         , c ~ IntensionalFunctorCF m
         , IntensionalMonad m
         )
      => IntensionalApplicative (StateT c s m) where
  type IntensionalApplicativePureC (StateT c s m) a =
        ( Typeable a
        , c a
        , IntensionalApplicativePureC m (a, s)
        )
  type IntensionalApplicativeApC (StateT c s m) a b =
        ( Typeable a
        , Typeable b
        , c (s ->%c m (a,s))
        , c (s ->%c (m ((a ->%c b),s)))
        , c (a ->%c b)
        , IntensionalApplicativePureC m (b,s)
        , IntensionalMonadBindC m ((a ->%c b),s) (b,s)
        , IntensionalMonadBindC m (a,s) (b,s)
        )
  itsPure = \%c x ->
    StateT (\%c s -> itsPure %@ (x,s))
  (%<*>) = \%%c (StateT (smab :: s ->%c (m (a ->%c b, s)))) (StateT (sa :: s ->%c m (a, s))) ->
    StateT $ \%c s ->
      intensional c do
        (ab,s') <- smab %@ s
        (a,s'') <- sa %@ s'
        itsPure %@ (ab %@ a, s'')

instance ( Typeable c
         , Typeable m
         , Typeable s
         , c ~ IntensionalFunctorCF m
         , IntensionalMonad m
         )
      => IntensionalMonad (StateT c s m) where
  type IntensionalMonadBindC (StateT c s m) a b =
        ( Typeable a
        , Typeable b
        , c (a ->%c StateT c s m b)
        , c (s ->%c m (a,s))
        , IntensionalMonadBindC m (a,s) (b,s)
        )
  itsBind = \%%c (StateT (ma :: s ->%c m (a,s))) (amb :: a ->%c StateT c s m b) ->
    (
    StateT $ \%c s ->
      intensional c do
        (a,s') <- ma %@ s
        let StateT smb = amb %@ a
        smb %@ s'
    ) :: StateT c s m b

instance IntensionalMonadTrans (StateT c s) where
  type IntensionalMonadTransLiftC (StateT c s) m a =
    ( Typeable a
    , Typeable s
    , c ~ IntensionalFunctorCF m
    , c s
    , c (m a)
    , IntensionalApplicativePureC m (a, s)
    , IntensionalMonadBindC m a (a, s)
    )
  itsLift = \%c m ->
    StateT $ \%c s -> intensional c do
      a <- m
      itsPure %@ (a, s)

itsGet :: forall c s m.
          ( Typeable s
          , c s
          , IntensionalApplicative m
          , IntensionalApplicativePureC m (s, s)
          )
       => StateT c s m s
itsGet = StateT $ \%c s -> itsPure %@ (s, s)

itsSet :: forall c s m.
          ( Typeable s
          , c s
          , IntensionalApplicative m
          , IntensionalApplicativePureC m ((), s)
          )
       => s ->%c StateT c s m ()
itsSet = \%c state -> StateT $ \%c _ -> itsPure %@ ((), state)
