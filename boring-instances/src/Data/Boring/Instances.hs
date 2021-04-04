{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE Trustworthy          #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Boring.Instances () where

import Data.Boring          (Absurd (..), Boring (..))
import Data.Constraint      (Dict (..))
import Data.Stream.Infinite (Stream (..))

import qualified Generics.SOP as SOP

-------------------------------------------------------------------------------
-- constraints
-------------------------------------------------------------------------------

instance c => Boring (Dict c) where
    boring = Dict

-------------------------------------------------------------------------------
-- streams
-------------------------------------------------------------------------------

instance Boring a => Boring (Stream a) where
    boring = boring :> boring

instance Absurd a => Absurd (Stream a) where
    absurd (x :> _) = absurd x

-------------------------------------------------------------------------------
-- generics-sop
-------------------------------------------------------------------------------

instance Boring a => Boring (SOP.I a) where
    boring = SOP.I boring

instance Boring b => Boring (SOP.K b a) where
    boring = SOP.K boring

instance Absurd a => Absurd (SOP.I a) where
    absurd = absurd . SOP.unI

instance Absurd b => Absurd (SOP.K b a) where
    absurd = absurd . SOP.unK

-------------------------------------------------------------------------------
-- representable
-------------------------------------------------------------------------------

{-
-- | If an index of 'Representable' @f@ is 'Absurd', @f a@ is 'Boring'.
boringRep :: (Representable f, Absurd (Rep f)) => f a
boringRep = tabulate absurd

-- | If an index of 'Representable' @f@ is 'Boring', @f@ is isomorphic to 'Identity'.
--
-- See also @Settable@ class in @lens@.
untainted :: (Representable f, Boring (Rep f)) => f a -> a
untainted = flip index boring
-}
