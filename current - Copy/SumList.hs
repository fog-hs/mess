{-# Language
 KindSignatures
,TypeOperators
,DataKinds
,PolyKinds
,GADTs
,TypeFamilies
,UndecidableInstances
,TypeFamilyDependencies
,AllowAmbiguousTypes
,FlexibleInstances
,RankNTypes,TypeApplications
,ScopedTypeVariables
,ConstraintKinds
#-}

module SumList where
import GHC.Exts
import TyFun
import TypeLevel
import Nonempty

data SumNonempty2 (fs :: Nonempty (k1 -> k2 -> c)) (a :: k1) (b :: k2) where
-- SumNonemptyAt :: Proxy (BoundedNat1 (Length1 fs)) -> (fs !!! n') a b -> SumNonempty2 fs a b
 SumNonempty2At :: Proxy n' -> (fs !!! n') a b -> SumNonempty2 fs a b

data SumNonempty1 (fs :: Nonempty (k1 -> c)) (a :: k1) where
-- SumNonemptyAt :: Proxy (BoundedNat1 (Length1 fs)) -> (fs !!! n') a -> SumNonempty1 fs a
 SumNonempty1At :: Proxy n' -> (fs !!! n') a -> SumNonempty1 fs a

data SumNonempty (fs :: Nonempty c) where
-- SumNonemptyAt :: Proxy (BoundedNat1 (Length1 fs)) -> (fs !!! n') -> SumNonempty fs
 SumNonemptyAt :: Proxy n' -> (fs !!! n') -> SumNonempty fs

egSumNonempty :: SumNonempty (Bool :| End Int)
egSumNonempty = SumNonemptyAt (Proxy :: Proxy (S1 Z1)) (1::Int)

--could use something like a gadt combining map and list?
-- taking the type parameter to apply to a list of types...

data DSum (xs :: Nonempty a) where
 DSum :: Proxy zs -> a -> Proxy ys -> DSum (zs ++| ((End a) |++ ys))

data DSum1 (xs :: Nonempty (k1 -> k2)) (a :: k) where
 DSum1 :: Proxy zs -> f a -> Proxy ys -> DSum1 (zs ++| ((End f) |++ ys)) a

egDSum :: DSum1 ('End Maybe) Int
egDSum = DSum1 (Proxy :: Proxy '[]) (Just 1) (Proxy :: Proxy '[])
{-
test :: DSum1 ('End Maybe) Int -> Int
test (DSum1 _ (Just a) _) = a
-}



data CSum1 (c :: (* -> *) -> Constraint) (xs :: Nonempty (* -> *)) (a :: *) where
 CSum1 :: c f => Proxy zs -> f a -> Proxy ys -> CSum1 c (zs ++| ((End f) |++ ys)) a

mapCSum1 :: (forall f. c f => f a -> b) -> CSum1 c xs a -> b
mapCSum1 f (CSum1 _ x _) = f x



-- make a version of Nonempty which has an extra arg giving the *value* it stores, using singletons
-- so that the kind Nonempty a xs specifies that xs of that kind is a 
data DSum1' (f :: x ~> (k1 -> k2)) (xs :: Nonempty x) (a :: k) where
 DSum1' :: Proxy zs -> (g @@ f) a -> Proxy ys -> DSum1' g (zs ++| ((End f) |++ ys)) a
{-
data DSum1'' (f :: x -> (k1 -> k2)) (xs :: Nonempty x) (a :: k) where
 DSum1'' :: Proxy zs -> (g f) a -> Proxy ys -> DSum1' g (zs ++| ((End f) |++ ys)) a
-}

data FSym0 :: k ~> (* -> *)
type instance Apply FSym0 a = F a

type F a = Maybe

data F'Sym0 :: k ~> (* -> *)
type instance Apply F'Sym0 a = F' a

type family F' (a :: k) = (b :: * -> *) where
 F' Int = Maybe
 F' a = Maybe




egDSum' :: DSum1' (F'Sym0) (() :| 'End ()) Int
egDSum' = DSum1' (Proxy :: Proxy '[()]) (Just 1) (Proxy :: Proxy '[])

test' :: DSum1' (F'Sym0) (() :| 'End ()) Int -> Int
test' (DSum1' _ (Just a) _) = a


{-
type family SumNonemptySym2 (fs :: BoundedNonempty b (k1 ~> k2 ~> c)) (n :: BoundedNat1 b) :: k1 ~> k2 ~> c where
  SumNonemptySym2 fs n = (fs !!! n) 
-}