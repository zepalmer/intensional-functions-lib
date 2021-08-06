{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Intensional.Monad.Trans.Coroutine.SuspensionFunctors
(
) where

import Control.Intensional.Functor
import Control.Intensional.Runtime
import Control.Intensional.WrappedIntensionalUtilFunctions

data Yield (c :: ConstraintFn) x y = Yield x y
instance (WrappableWith c '[x]) => IntensionalFunctor (Yield c x) where
  type IntensionalFunctorCF (Yield c x) = c
  type IntensionalFunctorMapC (Yield c x) a b =
      (c (HList '[a ->%c b]))
  itsFmap = \%c f (Yield x y) -> Yield x $ f %@ y

data Await c x y = Await (x ->%c y)
instance (WrappableWith c '[x]) => IntensionalFunctor (Await c x) where
  type IntensionalFunctorCF (Await c x) = c
  type IntensionalFunctorMapC (Await c x) a b =
      (c (HList '[a ->%c b]), c (HList '[a ->%c b, x ->%c a]))
  itsFmap = \%c f (Await fn) -> Await (itsCompose %@ f %@ fn)

