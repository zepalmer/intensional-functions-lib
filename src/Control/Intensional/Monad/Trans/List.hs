{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.List
( IMList(..)
, ListT(..)
, liftList
) where

-- | An intensional analogue to "ListT done right"
--   (https://wiki.haskell.org/ListT_done_right).

import Control.Intensional.Alternative
import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Monad.Trans
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime

data IMList (c :: ConstraintFn) m a where
  IMNil :: (IntensionalFunctorCF m ~ c) => IMList c m a
  IMCons :: (IntensionalFunctorCF m ~ c)
         => a -> m (IMList c m a) -> IMList c m a

newtype ListT c m a = ListT { runListT :: m (IMList c m a) }

liftList :: forall c m a.
            ( IntensionalMonad m
            , IntensionalFunctorCF m ~ c
            , IntensionalApplicativePureC m (IMList c m a)
            )
         => [a] ->%c ListT c m a
liftList = \%c xs -> case xs of
  [] -> ListT $ itsPure %@ IMNil
  x:xs' ->
    let ListT rest = liftList %@ xs' in
    ListT $ itsPure %@ IMCons x rest

instance (IntensionalFunctor m, IntensionalFunctorCF m ~ c)
    => IntensionalFunctor (IMList c m) where
  type IntensionalFunctorCF (IMList c m) = c
  type IntensionalFunctorMapC (IMList c m) a b =
    ( Typeable a, Typeable b, Typeable c
    , c ~ IntensionalFunctorCF m
    , c (a ->%c b)
    , IntensionalFunctorMapC m (IMList c m a) (IMList c m b)
    )
  itsFmap = \%%c fn imlst -> case imlst of
    IMNil -> IMNil
    IMCons el rest -> IMCons (fn %@ el) (itsFmap %@% (itsFmap %@ fn, rest))

instance (IntensionalFunctor m, IntensionalFunctorCF m ~ c)
    => IntensionalFunctor (ListT c m) where
  type IntensionalFunctorCF (ListT c m) = c
  type IntensionalFunctorMapC (ListT c m) a b =
    ( Typeable a, Typeable b, Typeable c
    , c ~ IntensionalFunctorCF m
    , c (a ->%c b)
    , IntensionalFunctorMapC m (IMList c m a) (IMList c m b)
    )
  itsFmap = \%%c fn (ListT mimlst) ->
    ListT $ itsFmap %@% (itsFmap %@ fn, mimlst)

instance (IntensionalMonad m, IntensionalFunctorCF m ~ c, Typeable c)
    => IntensionalApplicative (ListT c m) where
  type IntensionalApplicativePureC (ListT c m) a =
    (Typeable a, IntensionalApplicativePureC m (IMList c m a))
  itsPure = \%c x ->
    ListT $ itsPure %@ IMCons x (itsPure %@ IMNil)
  type IntensionalApplicativeApC (ListT c m) a b =
    ( Typeable a, Typeable b
    , c (ListT c m a)
    , IntensionalFunctorMapC (ListT c m) a b
    , IntensionalMonadBindC (ListT c m) (a ->%c b) b
    )
  (%<*>) = itsAp

instance (IntensionalMonad m, IntensionalFunctorCF m ~ c, Typeable c)
    => IntensionalMonad (ListT c m) where
  type IntensionalMonadBindC (ListT c m) a b =
    ( Typeable a, Typeable b
    , c (a ->%c ListT c m b)
    , c (ListT c m b ->%c m (IMList c m b))
    , IntensionalFunctorMapC m (IMList c m a) (IMList c m (ListT c m b))
    , c (m (IMList c m b))
    , IntensionalFunctorMapC
        m (IMList c m (ListT c m b)) (IMList c m (m (IMList c m b)))
    , IntensionalApplicativePureC m (IMList c m b)
    , IntensionalMonadBindC m (IMList c m b) (IMList c m b)
    , IntensionalMonadBindC m (IMList c m (m (IMList c m b))) (IMList c m b)
    )
  itsBind = \%%c mx fn -> joinListT %$ itsFmap %@% (fn, mx)

instance IntensionalMonadTrans (ListT c) where
  type IntensionalMonadTransLiftC (ListT c) m a =
    ( Typeable c
    , IntensionalMonad m
    , IntensionalFunctorCF m ~ c
    , IntensionalFunctorMapC m a (IMList c m a)
    , IntensionalApplicativePureC m (IMList c m a)
    )
  itsLift = \%c ma ->
    ListT $ itsFmap %@% ((\%c x -> IMCons x $ itsPure %@ IMNil), ma)

instance (IntensionalMonad m, IntensionalFunctorCF m ~ c, Typeable c)
    => IntensionalAlternative (ListT c m) where
  type IntensionalAlternativeEmptyC (ListT c m) a =
    (IntensionalApplicativePureC m (IMList c m a))
  itsEmpty = ListT $ itsPure %@ IMNil
  type IntensionalAlternativeChoiceC (ListT c m) a =
    ( Typeable a
    , c (m (IMList c m a))
    , IntensionalApplicativePureC m (IMList c m a)
    , IntensionalMonadBindC m (IMList c m a) (IMList c m a)
    )
  (%<|>) = \%%c (ListT xs) (ListT ys) -> ListT $ mimlistAppend %@% (xs, ys)

instance (IntensionalMonad m, IntensionalFunctorCF m ~ c, Typeable c)
    => IntensionalMonadPlus (ListT c m) where
  type IntensionalMonadPlusZeroC (ListT c m) a =
    IntensionalAlternativeEmptyC (ListT c m) a
  itsMzero = itsEmpty
  type IntensionalMonadPlusPlusC (ListT c m) a =
    IntensionalAlternativeChoiceC (ListT c m) a
  itsMplus = (%<|>)

joinListT :: forall c m a.
             ( MIMListAppendC c m a
             , c (ListT c m a ->%c m (IMList c m a))
             , IntensionalFunctorMapC m
                (IMList c m (ListT c m a)) (IMList c m (m (IMList c m a)))
             , IntensionalMonadBindC m
                (IMList c m (m (IMList c m a))) (IMList c m a)
             )
          => ListT c m (ListT c m a) ->%c ListT c m a
joinListT = \%c (ListT mimlst) ->
  ListT $ joinIMList %@
    (itsFmap %@% ((itsFmap %@ (\%c x -> runListT x)), mimlst))

joinIMList :: forall c m a.
              ( MIMListAppendC c m a
              , IntensionalMonadBindC m
                  (IMList c m (m (IMList c m a))) (IMList c m a)
              )
           => m (IMList c m (m (IMList c m a))) ->%c m (IMList c m a)
joinIMList = \%c mimlst -> intensional c do
  imlst <- mimlst
  case imlst of
    IMNil -> itsPure %@ IMNil
    IMCons xs mxss -> mimlistAppend %@% (xs, joinIMList %@ mxss)

type MIMListAppendC c m a =
  ( Typeable a
  , Typeable c
  , c (m (IMList c m a))
  , IntensionalMonad m
  , IntensionalFunctorCF m ~ c
  , IntensionalApplicativePureC m (IMList c m a)
  , IntensionalMonadBindC m (IMList c m a) (IMList c m a)
  )

mimlistAppend :: forall c m a.
                 ( MIMListAppendC c m a )
              => '[ m (IMList c m a),
                    m (IMList c m a)
                  ] ->%%c m (IMList c m a)
mimlistAppend = \%%c mxs mys -> intensional c do
  xs <- mxs
  case xs of
    IMNil -> mys
    IMCons x mxs' -> itsPure %@ IMCons x (mimlistAppend %@% (mxs', mys))
