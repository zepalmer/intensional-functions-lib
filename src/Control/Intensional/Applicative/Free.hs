{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Intensional.Applicative.Free (
  FreeIntensionalApplicative(..),
  fiaForget,
) where

import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Runtime

{- ========== Free Intensional Applicative ========== -}

data FreeIntensionalApplicative
        (c :: ConstraintFn)
        (f :: Type -> Type)
        (a :: Type)
     where
  FiaPure :: a
       -> FreeIntensionalApplicative c f a
  FiaFmap :: (a ->%c b)
       -> FreeIntensionalApplicative c f a
       -> FreeIntensionalApplicative c f b
  FiaAp :: FreeIntensionalApplicative c f (a ->%c b)
     -> FreeIntensionalApplicative c f a
     -> FreeIntensionalApplicative c f b
  deriving (Typeable)

{- ========== Free Intensional Applicative Instances ========== -}

instance ( Wrappable (IntensionalFunctorCF (FreeIntensionalApplicative c f))
         , Typeable f)
    => IntensionalFunctor (FreeIntensionalApplicative c f) where
  type IntensionalFunctorCF (FreeIntensionalApplicative c f) = c
  type IntensionalFunctorMapC (FreeIntensionalApplicative c f) a b =
    c (HList '[a ->%c b])
  itsFmap = \%c f a -> FiaFmap f a

instance ( Wrappable (IntensionalFunctorCF (FreeIntensionalApplicative c f))
         , Typeable f)
    => IntensionalApplicative (FreeIntensionalApplicative c f) where
  type IntensionalApplicativePureC (FreeIntensionalApplicative c f) a =
    (Typeable a)
  type IntensionalApplicativeApC (FreeIntensionalApplicative c f) a b =
    ( Typeable a, Typeable b
    , c (HList '[FreeIntensionalApplicative c f (a ->%c b)])
    )
  itsPure = \%c x -> FiaPure x
  (%<*>) = \%c f a -> FiaAp f a

{- ========== Free Intensional Applicative Utilities ========== -}

-- This routine maps the free intensional applicative onto a different
-- *extensional* applicative.  This demonstrates that the intensional
-- applicative need not follow the functor lap "fmap id === id" in order to be
-- coherent.
fiaForget :: (Applicative g) => FreeIntensionalApplicative c f a -> g a
fiaForget (FiaPure a) = pure a
fiaForget (FiaFmap f a) = fmap (forget f) (fiaForget a)
fiaForget (FiaAp f a) = (forget <$> fiaForget f) <*> (fiaForget a)

-- This routine maps from the free intensional applicative onto another
-- (potentially more equation-ful) intensional applicative.
-- fiaInterpret :: ( IntensionalApplicative g
--                 , c ~ IntensionalFunctorCF g
--                 , WrappableWith c '[a]
--                 )
--              => FreeIntensionalApplicative c f a
--              -> g a
-- fiaInterpret (FiaPure a) = ipure %@ a
-- fiaInterpret (FiaFmap f a) = ifmap %@ f %@ fiaInterpret a
-- fiaInterpret (FiaAp f a) = iap %@ fiaInterpret f %@ fiaInterpret a
-- ITSTODO: discuss: is this possible now?  It seems that we need to be able
-- to say something like
--   "forall a. (IntensionalApplicativePureC f a ==>
--                                IntensionalApplicativePureC g a"
-- which could perhaps be encoded in a typeclass or something.
