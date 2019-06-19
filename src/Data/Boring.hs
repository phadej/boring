{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE EmptyCase        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
-- | 'Boring' and 'Absurd' classes. One approach.
--
-- Different approach would be to have
--
-- @
-- -- none-one-tons semiring
-- data NOT = None | One | Tons
--
-- type family Cardinality (a :: *) :: NOT
--
-- class Cardinality a ~ None => Absurd a where ...
-- class Cardinality a ~ One  => Boring a where ...
-- @
--
-- This would make possible to define more instances, e.g.
--
-- @
-- instance (Mult (Cardinality a) (Cardinality b) ~ None) => Absurd (a, b) where ...
-- @
--
-- === Functions
--
-- Function is an exponential:
--
-- @
-- Cardinality (a -> b) ~ Exponent (Cardinality b) (Cardinality a)
-- @
--
-- or shortly @|a -> b| = |b| ^ |a|@. This gives us possible instances:
--
-- * @|a| = 0 => |a -> b| = m ^ 0 = 1@, i.e. @'Absurd' a => 'Boring' (a -> b)@, or
--
-- * @|b| = 1 => |a -> b| = 1 ^ n = 1@, i.e. @'Boring' b => 'Boring' (a -> b)@.
--
-- Both instances are 'Boring', but we chose to define the latter.
--
-- === Note about adding instances
--
-- At this moment this module misses a lot of instances,
-- please make a patch to add more. Especially, if the package is already
-- in the transitive dependency closure.
--
-- E.g. any possibly empty container @f@ has @'Absurd' a => 'Boring' (f a)@
--
module Data.Boring (
    -- * Classes
    Boring (..),
    Absurd (..),
    -- * More interesting stuff
    vacuous,
    boringRep,
    untainted,
    devoid,
    united,
    -- ** Dec
    --
    -- | @'Dec' a@ can be 'Boring' in two ways: When 'a' is 'Boring' or 'Absurd'.
    boringYes,
    absurdNo,
    ) where

import Prelude ()
import Prelude.Compat

import Control.Applicative   (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Compose  (Compose (..))
import Data.Functor.Product  (Product (..))
import Data.Functor.Sum      (Sum (..))
import Data.Functor.Rep      (Representable (..))
import Data.Constraint       (Dict (..))
import Data.List.NonEmpty    (NonEmpty (..))
import Data.Proxy            (Proxy (..))
import Data.Tagged           (Tagged (..))
import Data.Type.Dec         (Dec (..), Decidable (..))
import Data.Stream.Infinite  (Stream (..))
import GHC.Generics   hiding (Rep)

import qualified Data.Fin                  as Fin
import qualified Data.Nat                  as Nat
import qualified Data.Singletons.Bool      as Bool
import qualified Data.Type.Nat             as Nat
import qualified Data.Type.Nat.LE          as ZeroSucc
import qualified Data.Type.Nat.LE.ReflStep as ReflStep
import qualified Data.Vec.Lazy             as Vec
import qualified Data.Vec.Pull             as Vec.Pull
import qualified Data.Void                 as V
import qualified Generics.SOP              as SOP

#if MIN_VERSION_base(4,7,0)
import qualified Data.Coerce        as Co
import qualified Data.Type.Coercion as Co
import qualified Data.Type.Equality as Eq
#endif

-------------------------------------------------------------------------------
-- Boring
-------------------------------------------------------------------------------

-- | 'Boring' types which contains one thing, also
-- 'boring'. There is nothing interesting to be gained by
-- comparing one element of the boring type with another,
-- because there is nothing to learn about an element of the
-- boring type by giving it any of your attention.
--
-- /Boring Law:/
--
-- @
-- 'boring' == x
-- @
--
-- /Note:/ This is different class from @Default@.
-- @Default@ gives you /some/ value,
-- @Boring@ gives you an unique value.
--
-- Also note, that we cannot have instances for e.g.
-- 'Either', as both
-- @('Boring' a, 'Absurd' b) => Either a b@ and
-- @('Absurd' a, 'Boring' b) => Either a b@ would be valid instances.
--
-- Another useful trick, is that you can rewrite computations with
-- 'Boring' results, for example @foo :: Int -> ()@, __if__ you are sure
-- that @foo@ is __total__.
--
-- > {-# RULES "less expensive" foo = boring #-}
--
-- That's particularly useful with equality ':~:' proofs.
--
class Boring a where
    boring :: a

instance Boring () where
    boring = ()

instance Boring b => Boring (a -> b) where
    boring = const boring

instance Boring (Proxy a) where
    boring = Proxy

instance Boring a => Boring (Const a b) where
    boring = Const boring

instance Boring b => Boring (Tagged a b) where
    boring = Tagged boring

instance Boring a => Boring (Identity a) where
    boring = Identity boring

instance Boring a => Boring (SOP.I a) where
    boring = SOP.I boring

instance Boring b => Boring (SOP.K b a) where
    boring = SOP.K boring

instance Boring (f (g a)) => Boring (Compose f g a) where
    boring = Compose boring

instance (Boring (f a), Boring (g a)) => Boring (Product f g a) where
    boring = Pair boring boring

instance c => Boring (Dict c) where
    boring = Dict

instance (Boring a, Boring b) => Boring (a, b) where
    boring = (boring, boring)

instance (Boring a, Boring b, Boring c) => Boring (a, b, c) where
    boring = (boring, boring, boring)

instance (Boring a, Boring b, Boring c, Boring d) => Boring (a, b, c, d) where
    boring = (boring, boring, boring, boring)

instance (Boring a, Boring b, Boring c, Boring d, Boring e) => Boring (a, b, c, d, e) where
    boring = (boring, boring, boring, boring, boring)

instance Boring a => Boring (Stream a) where
    boring = boring :> boring

-- | Recall regular expressions, kleene star of empty regexp is epsilon!
instance Absurd a => Boring [a] where
    boring = []

-- | @'Maybe' a = a + 1@, @0 + 1 = 1@.
instance Absurd a => Boring (Maybe a) where
    boring = Nothing

#if MIN_VERSION_base(4,7,0)
-- | Coercibility is 'Boring' too.
instance Co.Coercible a b => Boring (Co.Coercion a b) where
    boring = Co.Coercion

-- | Homogeneous type equality is 'Boring' too.
instance a ~ b => Boring (a Eq.:~: b) where
    boring = Eq.Refl

# if MIN_VERSION_base(4,12,0)
-- | Heterogeneous type equality is 'Boring' too.
instance a Eq.~~ b => Boring (a Eq.:~~: b) where
    boring = Eq.HRefl
# endif
#endif

-------------------------------------------------------------------------------
-- vec + fin + singleton-bool
-------------------------------------------------------------------------------

instance n ~ 'Nat.Z => Boring (Vec.Vec n a) where
    boring = Vec.empty

instance n ~ 'Nat.Z => Boring (Vec.Pull.Vec n a) where
    boring = Vec.Pull.empty

instance n ~ ('Nat.S 'Nat.Z) => Boring (Fin.Fin n) where
    boring = Fin.boring

-- singletons are boring

-- | @since 0.1.3
instance Nat.SNatI n => Boring (Nat.SNat n) where
    boring = Nat.snat

-- | @since 0.1.3
instance Bool.SBoolI b => Boring (Bool.SBool b) where
    boring = Bool.sbool

-- | @since 0.1.3
instance ZeroSucc.LE n m => Boring (ZeroSucc.LEProof n m) where
    boring = ZeroSucc.leProof

-- | @since 0.1.3
instance (ZeroSucc.LE n m, Nat.SNatI m) => Boring (ReflStep.LEProof n m) where
    boring = ReflStep.fromZeroSucc ZeroSucc.leProof

-------------------------------------------------------------------------------
-- Generics
-------------------------------------------------------------------------------

instance Boring (U1 p) where
    boring = U1

instance Boring c => Boring (K1 i c p) where
    boring = K1 boring

instance Boring (f p) => Boring (M1 i c f p) where
    boring = M1 boring

instance (Boring (f p), Boring (g p)) => Boring ((f :*: g) p) where
    boring = boring :*: boring

instance Boring p => Boring (Par1 p) where
    boring = Par1 boring

instance Boring (f p) => Boring (Rec1 f p) where
    boring = Rec1 boring

instance Boring (f (g p)) => Boring ((f :.: g) p) where
    boring = Comp1 boring

-------------------------------------------------------------------------------
-- Absurd
-------------------------------------------------------------------------------

-- | The 'Absurd' type is very exciting, because if somebody ever gives you a
-- value belonging to it, you know that you are already dead and in Heaven and
-- that anything you want is yours.
--
-- Similarly as there are many 'Boring' sums, there are many 'Absurd' products,
-- so we don't have 'Absurd' instances for tuples.
class Absurd a where
    absurd :: a -> b

instance Absurd V.Void where
    absurd = V.absurd

instance (Absurd a, Absurd b) => Absurd (Either a b) where
    absurd (Left a) = absurd a
    absurd (Right b) = absurd b

instance Absurd a => Absurd (NonEmpty a) where
    absurd (x :| _) = absurd x

instance Absurd a => Absurd (Stream a) where
    absurd (x :> _) = absurd x

instance Absurd a => Absurd (Identity a) where
    absurd = absurd . runIdentity

instance Absurd (f (g a)) => Absurd (Compose f g a) where
    absurd = absurd . getCompose

instance (Absurd (f a), Absurd (g a)) => Absurd (Sum f g a) where
    absurd (InL fa) = absurd fa
    absurd (InR ga) = absurd ga

instance Absurd b => Absurd (Const b a) where
    absurd = absurd . getConst

instance Absurd a => Absurd (Tagged b a) where
    absurd = absurd . unTagged

instance Absurd a => Absurd (SOP.I a) where
    absurd = absurd . SOP.unI

instance Absurd b => Absurd (SOP.K b a) where
    absurd = absurd . SOP.unK

instance n ~ 'Nat.Z => Absurd (Fin.Fin n) where
    absurd = Fin.absurd

instance (ZeroSucc.LE m n, n' ~ 'Nat.S n) => Absurd (ZeroSucc.LEProof n' m) where
    absurd = ZeroSucc.leSwap' ZeroSucc.leProof

instance (ZeroSucc.LE m n, n' ~ 'Nat.S n, Nat.SNatI n) => Absurd (ReflStep.LEProof n' m) where
    absurd = ZeroSucc.leSwap' ZeroSucc.leProof . ReflStep.toZeroSucc

-------------------------------------------------------------------------------
-- Generics
-------------------------------------------------------------------------------

instance Absurd (V1 p) where
    absurd v = case v of {}

instance Absurd c => Absurd (K1 i c p) where
    absurd = absurd . unK1

instance Absurd (f p) => Absurd (M1 i c f p) where
    absurd = absurd . unM1

instance (Absurd (f p), Absurd (g p)) => Absurd ((f :+: g) p) where
    absurd (L1 a) = absurd a
    absurd (R1 b) = absurd b

instance Absurd p => Absurd (Par1 p) where
    absurd = absurd . unPar1

instance Absurd (f p) => Absurd (Rec1 f p) where
    absurd = absurd . unRec1

instance Absurd (f (g p)) => Absurd ((f :.: g) p) where
    absurd = absurd . unComp1

-------------------------------------------------------------------------------
-- More interesting stuff
-------------------------------------------------------------------------------

-- | If 'Absurd' is uninhabited then any 'Functor' that holds only
-- values of type 'Absurd' is holding no values.
vacuous :: (Functor f, Absurd a) => f a -> f b
vacuous = fmap absurd

-- | If an index of 'Representable' @f@ is 'Absurd', @f a@ is 'Boring'.
boringRep :: (Representable f, Absurd (Rep f)) => f a
boringRep = tabulate absurd

-- | If an index of 'Representable' @f@ is 'Boring', @f@ is isomorphic to 'Identity'.
--
-- See also @Settable@ class in @lens@.
untainted :: (Representable f, Boring (Rep f)) => f a -> a
untainted = flip index boring

-- | There is a field for every type in the 'Absurd'. Very zen.
--
-- @
-- 'devoid' :: 'Absurd' s => Over p f s s a b
-- @
-- type Over p f s t a b = p a (f b) -> s -> f t
devoid :: Absurd s => p a (f b) -> s -> f s
devoid _ = absurd

-- | We can always retrieve a 'Boring' value from any type.
--
-- @
-- 'united' :: 'Boring' a => Lens' s a
-- @
united :: (Boring a, Functor f) => (a -> f a) -> s -> f s
united f v = v <$ f boring

-------------------------------------------------------------------------------
-- Dec
-------------------------------------------------------------------------------

-- | This relies on the fact that @a@ is /proposition/ in h-Prop sense.
--
-- @since 0.1.3
instance Decidable a => Boring (Dec a) where
    boring = decide

-- | 'Yes', it's 'boring'.
--
-- @since 0.1.3
boringYes :: Boring a => Dec a
boringYes = Yes boring

-- | 'No', it's 'absurd'.
--
-- @since 0.1.3
absurdNo :: Absurd a => Dec a
absurdNo = No absurd
