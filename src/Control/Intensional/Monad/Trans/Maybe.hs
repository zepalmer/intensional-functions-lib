{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.Maybe
( MaybeT(..)
) where

-- | An intensional analogue to Control.Monad.Trans.Maybe.

import Control.Intensional.Alternative
import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Monad.Trans
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime

newtype MaybeT (c :: ConstraintFn) (m :: Type -> Type) a =
  MaybeT { runMaybeT :: m (Maybe a) }

deriving instance (Eq (m (Maybe a))) => (Eq (MaybeT c m a))
deriving instance (Ord (m (Maybe a))) => (Ord (MaybeT c m a))

instance ( Typeable c
         , IntensionalFunctorCF m ~ c
         , IntensionalMonad m
         )
      => IntensionalFunctor (MaybeT c m) where
    type IntensionalFunctorCF (MaybeT c m) = c
    type IntensionalFunctorMapC (MaybeT c m) a b =
        ( Typeable a
        , Typeable b
        , c (a ->%c b)
        , IntensionalApplicativePureC m (Maybe b)
        , IntensionalMonadBindC m (Maybe a) (Maybe b)
        )
    itsFmap = \%%c (ab :: a ->%c b) (MaybeT (ma :: m (Maybe a))) ->
      MaybeT $ intensional c do
        maybea <- ma
        case maybea of
          Nothing -> itsPure %@ Nothing
          Just a -> itsPure %$ Just (ab %@ a)

instance ( Typeable c
         , IntensionalFunctor (MaybeT c m)
         , IntensionalApplicative m
         , IntensionalFunctorCF m ~ c
         , IntensionalFunctorCF (MaybeT c m) ~ c
         )
      => IntensionalApplicative (MaybeT c m) where
    type IntensionalApplicativePureC (MaybeT c m) a =
      (IntensionalApplicativePureC m (Maybe a))
    type IntensionalApplicativeApC (MaybeT c m) a b =
      ( Typeable a
      , IntensionalApplicativePureC m
          (Maybe a ->%c (Maybe (a ->%c b)) ->%c Maybe b)
      , IntensionalApplicativeApC m (Maybe (a ->%c b)) (Maybe b)
      , IntensionalApplicativeApC m
          (Maybe a) (Maybe (a ->%c b) ->%c Maybe b)
      , c (Maybe a)
      )
    itsPure = \%%c x -> MaybeT $ itsPure %@ Just x
    (%<*>) = \%%c (MaybeT fab) (MaybeT fa) ->
      let maybeApply =
            itsPure %@ \%c maybea maybeab ->
              case maybea of
                Nothing -> Nothing
                Just a ->
                  case maybeab of
                    Nothing -> Nothing
                    Just ab -> Just $ ab %@ a
      in
      MaybeT $ (%<*>) %@% (((%<*>) %@% (maybeApply, fa)), fab)

instance ( IntensionalMonad m
         , IntensionalApplicative (MaybeT c m)
         , IntensionalFunctorCF m ~ c
         )
      => IntensionalAlternative (MaybeT c m) where
    type IntensionalAlternativeEmptyC (MaybeT c m) a =
        IntensionalApplicativePureC m (Maybe a)
    type IntensionalAlternativeChoiceC (MaybeT c m) a =
        ( Typeable a
        , c (MaybeT c m a)
        , IntensionalApplicativePureC m (Maybe a)
        , IntensionalMonadBindC m (Maybe a) (Maybe a)
        )
    itsEmpty = MaybeT $ itsPure %@ Nothing
    (%<|>) = \%%c x y ->
        MaybeT $ intensional c do
            v <- runMaybeT x
            case v of
                Nothing -> runMaybeT y
                Just _ -> itsPure %@ v


instance ( Typeable c
         , IntensionalMonad m
         , IntensionalFunctorCF m ~ c
         , IntensionalFunctorCF (MaybeT c m) ~ c
         )
      => IntensionalMonad (MaybeT c m) where
    type IntensionalMonadBindC (MaybeT c m) a b =
        ( Typeable a
        , Typeable b
        , c (a ->%c MaybeT c m b)
        , IntensionalApplicativePureC m (Maybe b)
        , IntensionalMonadBindC m (Maybe a) (Maybe b)
        )
    itsBind = \%%c (MaybeT ma) amb -> MaybeT $ intensional c do
        maybeA <- ma
        case maybeA of
            Nothing -> itsPure %@ Nothing
            Just a -> runMaybeT $ amb %@ a

instance ( Typeable c
         , IntensionalAlternative (MaybeT c m)
         , IntensionalFunctorCF m ~ c
         , IntensionalMonad m
         )
      => IntensionalMonadPlus (MaybeT c m) where
    type IntensionalMonadPlusZeroC (MaybeT c m) a =
        IntensionalAlternativeEmptyC (MaybeT c m) a
    type IntensionalMonadPlusPlusC (MaybeT c m) a =
        IntensionalAlternativeChoiceC (MaybeT c m) a
    itsMzero = itsEmpty
    itsMplus = (%<|>)

instance IntensionalMonadTrans (MaybeT c) where
  type IntensionalMonadTransLiftC (MaybeT c) m a =
    ( Typeable a
    , c ~ IntensionalFunctorCF m
    , IntensionalFunctorMapC m a (Maybe a)
    )
  itsLift = \%c m ->
    MaybeT $ itsFmap %@% (\%c x -> Just x, m)
