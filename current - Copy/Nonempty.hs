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

module Nonempty where

import TyFun
import TypeLevel
import GHC.Exts

data Nonempty a = a :| Nonempty a | End a deriving (Eq,Show)

infixr 0 :|

type family (:||) (x :: a) (xs :: [a]) = (ys :: Nonempty a) | ys -> xs x where
-- (:||) x '[] = End x
-- (:||) x (y : xs) = x :| (y :|| xs)

type family (++|) (xs :: [a]) (ys :: Nonempty a) = (zs :: Nonempty a) where
 (++|) ('[] :: [a]) ys = ys
 (++|) (x : xs) ys = x :| (xs ++| ys)

type family (+|+) (xs :: Nonempty a) (ys :: Nonempty a) = (zs :: Nonempty a) where
 (+|+) (End a) ys = a :| ys
 (+|+) (x :| xs) ys = x :| (xs +|+ ys)

type family (|++) (xs :: Nonempty a) (ys :: [a]) = (zs :: Nonempty a) where
 (|++) xs '[] = xs
 (|++) xs (y : ys) = (xs +|+ End y) |++ ys

instance Functor Nonempty where
-- fmap f (End a) = End (f a)
 fmap f (x :| xs) = f x :| (fmap f xs)

-- Nats live here because otherwise its circular modules

type Nat1 = Nonempty ()
type Z1 = (End '() :: Nat1)
type S1 = (:|) '()

-- Map1

type family Map1 (f :: a ~> b) (xs :: Nonempty a) = (ys :: Nonempty b) | ys -> xs f where
 Map1 f (End a) = End (f @@ a)
 Map1 f (x :| xs) = f @@ x :| Map1 f xs

type family Map (f :: a ~> b) (xs :: [] a) = (ys :: [] b) where
 Map1 f '[] = '[]
 Map1 f (x : xs) = f @@ x : Map f xs


-- Loop; Fold Symbols using (.)

type family Loop1 (xs :: Nonempty (* ~> *)) a :: * where
 Loop1 (End f) a = f @@ a
 Loop1 (x ':| xs) a = x @@ (Loop1 xs a)
-- cant write this using Foldr1?

-- Tails
type family Tails1 (xs :: Nonempty k) = (ys :: Nonempty (Nonempty k)) | ys -> xs where
 Tails1 (End a) = (End (End a))
 Tails1 xs = xs ':| Tails1 (Tail1' xs) 

type family Tail1 (xs :: Nonempty k) :: Maybe (Nonempty k) where
 Tail1 (End a) = Nothing
 Tail1 (x ':| xs) = Just (Tail1' (x ':| xs))

type family Tail1' (xs :: Nonempty k) :: (Nonempty k) where
 Tail1' (x ':| End z) = End x
 Tail1' (x ':| xs) = xs

type family Tail1'' (xs :: Nonempty k) :: ([] k) where
 Tail1'' (End z) = '[]
 Tail1'' (x ':| xs) = FromNonempty xs

type family FromNonempty (xs :: Nonempty a) :: [a] where
 FromNonempty (End a) = a : '[]
 FromNonempty (x:|xs) = x : FromNonempty xs

type family ToNonempty (xs :: [] a) :: Nonempty a where
 ToNonempty (a ': '[]) = End a
 ToNonempty (x:xs) = x :| ToNonempty xs

type family TailOf (xs :: [] k) (ys :: Nonempty k) where 
 TailOf '[] ys = 'True
 TailOf xs ys = Elem (ToNonempty xs) (Tail1'' (Tails1 ys)) 

type family Elem1 (a :: k) (xs :: Nonempty k) :: Bool where
 Elem1 a (End a) = 'True
 Elem1 a (a :| xs) = 'True
 Elem1 a (x :| xs) = Elem1 a xs

type family Elem (a :: k) (xs :: [] k) :: Bool where
 Elem a '[] = 'False
 Elem a (a : xs) = 'True
 Elem a (x : xs) = Elem a xs
 
--Elem fs (Tail1 (Tails1 gs)) 

{-
class TailOf_class xs ys where
 type TailOf xs ys :: Bool

--Elem fs (Tail1 (Tails1 gs)) 
instance TailOf_class (xs :: [] k) (ys :: Nonempty k) where
 TailOf xs ys = 
-}

-- Inits

type family Inits1 (xs :: Nonempty k) = (ys :: Nonempty (Nonempty k)) | ys -> xs where
 Inits1 (End a) = (End (End a))
 Inits1 xs = xs ':| Inits1 (Init1' xs) 

type family Init1 (xs :: Nonempty k) :: Maybe (Nonempty k) where
 Init1 (End a) = Nothing
 Init1 (x ':| xs) = Just (Init1' (x ':| xs))

type family Init1' (xs :: Nonempty k) :: (Nonempty k) where
 Init1' (x ':| y :| End z) = (x ':| End y)
 Init1' (x ':| xs) = (x ':| Init1' xs)

type family Last1 (xs :: Nonempty k) = (x :: k)  where
 Last1 (End a) = a
 Last1 (x ':| xs) = Last1 xs
{-
what if money couldnt buy political power? if suddenly dollars no longer equals votes - or buying out a judge or jury, would it suddenly crash in value? 
if you really cared about money being something to be coverted by the super wealthy
you would support the ability to puchace entire cities!
if money could no longer perpatuate a global wage slavery,
by carefully controling the afordability of housing and forcing out 
anyone not complicit in gross corruption, in order to hone a taskforce of bastards, then money would hardely have any value at all! 
-}
-- Length1

type family Length1 (xs :: Nonempty a) = (ys :: Nat1) where
 Length1 xs = Map1 (ConstSym1 '()) xs

-- (!!!)

type family Head1 (xs :: Nonempty a) :: a where
 Head1 (End x) = x
 Head1 (x ':| xs) = x

type family Drop1 (n :: Nat1) (xs :: Nonempty a) :: Nonempty a where
 Drop1 (_ ':| n) (x ':| xs) = Drop1 n xs
 Drop1 (End _) xs = xs

type family (!!!) (xs :: Nonempty a) (n :: Nat1) :: a where
 (!!!) xs n = Head1 (Drop1 n xs)
