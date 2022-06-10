{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.Writer
( WriterT(..)
) where

-- | An intensional analogue to Control.Monad.Trans.State.

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Monad.Trans
import Control.Intensional.Runtime
import Data.Monoid

newtype WriterT (c :: ConstraintFn) w (m :: Type -> Type) a =
  WriterT { runWriterT :: m (a,w) }

deriving instance
     (Eq (m (a,w)))
  => (Eq (WriterT c w m a))
deriving instance
     (Ord (m (a,w)))
  => (Ord (WriterT c w m a))

instance (Monoid w) => IntensionalMonadTrans (WriterT c w) where
  type IntensionalMonadTransLiftC (WriterT c w) m a =
    ( Typeable a
    , Typeable w
    , c ~ IntensionalFunctorCF m
    , c w
    , c (m a)
    , IntensionalFunctorMapC m a (a,w)
    )
  itsLift = \%c m -> WriterT $ itsFmap %@% (\%c m -> (m,mempty), m)

itsTell :: forall c w m.
           ( IntensionalMonad m
           , IntensionalApplicativePureC m ((), w)
           )
        => w ->%c WriterT c w m ()
itsTell = \%c w -> WriterT $ itsPure %@ ((), w)

itsListen :: forall c w m a.
             ( IntensionalMonad m
             , IntensionalFunctorCF m ~ c
             , IntensionalApplicativePureC m ((a, w), w)
             , IntensionalMonadBindC m (a, w) ((a, w), w)
             )
          => WriterT c w m a ->%c WriterT c w m (a, w)
itsListen = \%c m ->
  WriterT $ intensional c do
    (a, w) <- runWriterT m
    itsPure %$ ((a, w), w)

itsListens :: forall c w m a b.
              ( Typeable c, Typeable w, Typeable b
              , IntensionalMonad m
              , IntensionalFunctorCF m ~ c
              , c (w ->%c b)
              , IntensionalApplicativePureC m ((a, b), w)
              , IntensionalMonadBindC m (a, w) ((a, b), w)
              )
           => '[w ->%c b, WriterT c w m a] ->%%c WriterT c w m (a, b)
itsListens = \%%c f m ->
  WriterT $ intensional c do
    (a, w) <- runWriterT m
    itsPure %$ ((a, f %@ w), w)

itsPass :: forall c w m a.
           ( IntensionalMonad m
           , IntensionalFunctorCF m ~ c
           , IntensionalApplicativePureC m (a ,w)
           , IntensionalMonadBindC m ((a, w ->%c w), w) (a, w)
           )
        => WriterT c w m (a, w ->%c w) ->%c WriterT c w m a
itsPass = \%c m ->
  WriterT $ intensional c do
    ((a, f), w) <- runWriterT m
    itsPure %$ (a, f %@ w)

itsCensor :: forall c w m a.
             ( Typeable c, Typeable w
             , IntensionalMonad m
             , IntensionalFunctorCF m ~ c
             , c (w ->%c w)
             , IntensionalApplicativePureC m (a, w)
             , IntensionalMonadBindC m (a, w) (a, w)
             )
          => '[w ->%c w, WriterT c w m a] ->%%c WriterT c w m a
itsCensor = \%%c f m ->
  WriterT $ intensional c do
    (a, w) <- runWriterT m
    itsPure %$ (a, f %@ w)
