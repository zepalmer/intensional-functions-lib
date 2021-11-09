{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |An implementation of a coroutine transformer for intensional monads.  Based
--  on Control.Monad.Coroutine by Mario Blazevic.

module Control.Intensional.Monad.Trans.Coroutine
( CoroutineT(..)
, suspend
, CoroutineStepResult
) where

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.Monad.Trans
import Control.Intensional.Runtime

-- |Intensional monad transformer for suspending, resumable computations.
newtype CoroutineT (c :: ConstraintFn) s m r = CoroutineT {
  resume :: m (Either (s (CoroutineT c s m r)) r)
}

-- |The outcome of a computation when it returns control: it is either suspended
--  (the Left case) or completed (the Right case).
type CoroutineStepResult c s m r = Either (s (CoroutineT c s m r)) r

deriving instance (Eq (m (CoroutineStepResult c s m r)))
  => Eq (CoroutineT c s m r)
deriving instance (Ord (m (CoroutineStepResult c s m r)))
  => Ord (CoroutineT c s m r)

instance ( IntensionalMonad m
         , IntensionalFunctor s
         , Typeable s
         , IntensionalFunctorCF m ~ c
         , IntensionalFunctorCF s ~ c
         )
    => IntensionalFunctor (CoroutineT c s m) where
  type IntensionalFunctorCF (CoroutineT c s m) = c
  type IntensionalFunctorMapC (CoroutineT c s m) a b =
    ( c (HList '[(a ->%c b) ->%c
          (CoroutineStepResult c s m a ->%c CoroutineStepResult c s m b)])
    , c (HList '[
          (a ->%c b) ->%c
              (CoroutineStepResult c s m a ->%c CoroutineStepResult c s m b),
          (a ->%c b)
        ])
    , c (HList '[a ->%c b])
    , IntensionalFunctorMapC m
        (CoroutineStepResult c s m a)
        (CoroutineStepResult c s m b)
    , IntensionalFunctorMapC s (CoroutineT c s m a) (CoroutineT c s m b)
    )
  itsFmap = \%c f x ->
    CoroutineT (itsFmap %@ (apply %@ f) %@ (resume x))
    where apply = \%c fc r ->
            case r of
              Right x -> Right (fc %@ x)
              Left s -> Left (itsFmap %@ (itsFmap %@ fc) %@ s)

instance ( IntensionalMonad m
         , IntensionalFunctor s
         , Typeable s
         , IntensionalFunctorCF m ~ c
         , IntensionalFunctorCF s ~ c
         )
    => IntensionalApplicative (CoroutineT c s m) where

  type IntensionalApplicativePureC (CoroutineT c s m) a =
    ( IntensionalApplicativePureC m (CoroutineStepResult c s m a)
    , Typeable a)
  itsPure = \%c x ->
    CoroutineT $ itsPure %@ Right x

  type IntensionalApplicativeApC (CoroutineT c s m) a b =
    ( Typeable a, Typeable b
    , c (HList '[CoroutineT c s m (a ->%c b)])
    , c (HList
          '[(a ->%c b) ->%c (CoroutineStepResult c s m a)
                       ->%c (CoroutineStepResult c s m b)
           ])
    , c (HList
          '[ (a ->%c b) ->%c (CoroutineStepResult c s m a)
                        ->%c (CoroutineStepResult c s m b)
           , a ->%c b
           ])
    , c (HList '[a ->%c b])
    , c (HList '[CoroutineT c s m a])
    , IntensionalFunctorMapC m
        (CoroutineStepResult c s m a) (CoroutineStepResult c s m b)
    , IntensionalFunctorMapC s (CoroutineT c s m a) (CoroutineT c s m b)
    , IntensionalMonadBindC (CoroutineT c s m) (a ->%c b) b
    )
  (%<*>) = \%c f x -> itsAp %@ f %@ x

instance ( IntensionalMonad m
         , IntensionalFunctor s
         , Typeable s
         , IntensionalFunctorCF m ~ c
         , IntensionalFunctorCF s ~ c
         )
    => IntensionalMonad (CoroutineT c s m) where
  type IntensionalMonadBindC (CoroutineT c s m) a b =
    ( Typeable a, Typeable b
    , c (HList
          '[(a ->%c CoroutineT c s m b) ->%c
              (CoroutineStepResult c s m a ->%c m (CoroutineStepResult c s m b))
           ])
    , c (HList
          '[CoroutineT c s m a
           ,(a ->%c CoroutineT c s m b) ->%c
              (CoroutineStepResult c s m a ->%c m (CoroutineStepResult c s m b))
           ])
    , c (HList '[a ->%c (CoroutineT c s m b)])
    , IntensionalFunctorMapC s (CoroutineT c s m a) (CoroutineT c s m b)
    , IntensionalApplicativePureC m (CoroutineStepResult c s m b)
    , IntensionalMonadBindC m
        (CoroutineStepResult c s m a) (CoroutineStepResult c s m b)
    )
  itsBind = \%c x f ->
    CoroutineT (itsBind %@ (resume x) %@ (apply %@ f))
      where apply = \%c fc r ->
              case r of
                Right v -> resume $ fc %@ v
                Left s ->
                  itsPure %@
                    (Left (itsFmap %@ (\%c x -> itsBind %@ x %@ fc) %@ s))

instance IntensionalMonadTrans (CoroutineT c s) where
  type IntensionalMonadTransLiftC (CoroutineT c s) m a =
    ( Typeable a, Typeable s, IntensionalFunctorCF m ~ c
    , IntensionalFunctorMapC m a (CoroutineStepResult c s m a))
  itsLift = \%c ma ->
    CoroutineT $ itsFmap %@ (\%c x -> Right x) %@ ma

-- |Suspends a coroutine.
suspend :: ( IntensionalMonad m, IntensionalFunctor s
           , c ~ IntensionalFunctorCF m, c ~ IntensionalFunctorCF s
           , IntensionalApplicativePureC m (CoroutineStepResult c s m a)
           )
        => s (CoroutineT c s m a) -> CoroutineT c s m a
suspend s = CoroutineT $ itsPure %@ (Left s)
