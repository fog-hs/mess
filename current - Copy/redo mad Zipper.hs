{-# Language 
GADTs,
DataKinds,
PolyKinds,
TypeFamilies,
DatatypeContexts,
MultiParamTypeClasses,
UndecidableInstances,
DefaultSignatures,
RankNTypes,
QuantifiedConstraints,
FlexibleContexts,
FlexibleInstances,
FunctionalDependencies,
TypeOperators,
AllowAmbiguousTypes,
ScopedTypeVariables,
TypeApplications,
ConstraintKinds,
TypeFamilyDependencies
--OverlappingInstances
--UndecidableSuperClasses
#-}

import Data.Functor.Identity
import SumList
import TyFun
import Nonempty
import Data.Bifunctor

import GHC.TypeLits (TypeError(..),ErrorMessage(..))


data Nesting  (fs :: [] (* -> *)) (a :: *) where
 Nest  :: (Set f,Functor f) => f (Nesting  fs a) -> Nesting  (f : fs) a
 Subject :: (Set f,Functor f) => Nesting  '[] a

data Nesting1  (fs :: Nonempty (* -> *)) (a :: *) where
 Nest1    :: (Get f,Set f,Functor f) => f (Nesting1 fs a) -> Nesting1 (f :| fs) a
 Subject1 :: (Get f,Set f,Functor f) => f           a  -> Nesting1 (End f)   a

instance Functor (Nesting1 fs) 

instance (Eq a,forall b. (Eq b => Eq (f b))) => Eq (Nesting1 (End f) a) where
 (Subject1 xs) == (Subject1 ys) = xs == ys
 
instance (Eq a,forall b. (Eq b => Eq (f b)),Eq (Nesting1 fs a)) => Eq (Nesting1 (f:|fs) a) where
 (Nest1 xs) == (Nest1 ys) = xs == ys


--

-- IMPORTANT COMMENT
-- until there is a zipper over nest
-- it is expensive to use headmap to descend through layers
-- a vertical zipper should be at the lowest level
-- until a row is finished and then it should move up
-- so that the nesxt collum can be attactched/detatched at a higher level.

headMap :: (Set f,Get f) => (a -> a) -> f a -> f a
headMap g = set . f g . get
 where
  f :: (a -> a) -> Base (BaseTagOf f) a f -> Base (BaseTagOf f) a f
  f g = baseValueMap g

class Insert fs gs where
 insert :: (fs -> fs) -> gs -> gs

instance Insert (Nesting1 fs x) (Nesting1 gs x) where
 insert x (Nest1 y) = Nest1 $ headMap (insert x) y 
 insert _ (Subject1 _) = error "this should have matched the lower specificty Insert instance, this shouldnt be reachable because of the TailOf constraint"

instance () => Insert (g (Nesting1 gs x)) (Nesting1 (g:|gs) x) where
 insert f (Nest1 xs) = Nest1 (f xs) -- set.(toSuccess a)
-- well thats wrong, should be recursing.... needs to call insert... gives a different constraint...
-- wait thats what the above instance does... commenting this out...
-- fuck, it seems to use both instances, this seems wrong


-- BaseTag 

data BaseTag = StreamTag (* -> *) | LinearTag (* -> *) | StackTag  (* -> *) | NestedTag (Nonempty BaseTag) -- use nonempty for Nested.

type family GetTagParam (b :: BaseTag) :: * -> * where
 GetTagParam (StreamTag r) = r
 GetTagParam (LinearTag r) = r
 GetTagParam (StackTag  r) = r

-- Base

data Base (tag :: BaseTag) (a :: *) (s :: * -> *) where
 Success :: EvalSuccess s tag a -> Base tag a s
 Fail    :: EvalFail    tag a   -> Base tag a s

-- cant cast from a -> b as there is also an `a' applied to `s'
baseValueMap :: (a -> a) -> Base tag a s -> Base tag a s
baseValueMap f (Success x) = Success (successValueMap f x)
baseValueMap f (Fail x) = Fail (failValueMap f x)

baseStateMap :: (s a -> s' a) -> Base tag a s -> Base tag a s'
baseStateMap f (Success x) = Success (successMapState f x)
baseStateMap _ (Fail x) = Fail x


class Transformation (t :: * -> (* -> *) -> *) where
 transform :: (f a -> g a) -> t a f -> t a g

instance Transformation (Base tag) where
 transform = baseStateMap

-- EvalFail 

data EvalFailSym :: tag ~> (* -> *)
type instance Apply EvalFailSym t = EvalFail t

data EvalFail (tag :: BaseTag) a :: * where
 LinearFail :: Functor r => r a -> EvalFail (LinearTag r)  a
 StackFail  :: Functor r =>        EvalFail (StackTag  r)  a
 NestedFail :: Nesting1 (MakeFail xs) a 
                   -> EvalFail (NestedTag xs) a  

failValueMap :: (a -> a) -> EvalFail tag a -> EvalFail tag a   
failValueMap f (LinearFail ra) = LinearFail (fmap f ra) 
failValueMap f StackFail = StackFail
failValueMap f (NestedFail x) = undefined


type MakeFail xs = Map1 (TyCon1 EvalFail) xs

type MakeFail' xs = Map1 (TyCon1 EvalFail) (Map1 BaseTagOfSym0 xs)

data NestFail  (fs :: Nonempty (* -> *)) (a :: *) where
 NestFail    :: (Set f,Functor f) => (f) (NestFail fs a) -> NestFail (f :| fs) a
 NestSubject :: (Set f,Functor f) => (f)              a  -> NestFail (End f) a

instance Functor (NestFail  fs) 

instance Functor (EvalFail tag) where
 fmap f (LinearFail ra) = LinearFail (fmap f ra)
 fmap _ (StackFail    ) = StackFail  
 fmap f (NestedFail xs) = NestedFail (fmap f xs)

-- EvalSuccess 

data EvalSuccess (s :: * -> *) (tag :: BaseTag) (a :: *) :: * where
 --(Stream r)   a s = (r a,s) 
 LinearSuccess :: Functor r => (r a,s a) -> EvalSuccess s (LinearTag r) a
 StackSuccess  :: Functor r => (r a,s a) -> EvalSuccess s (StackTag  r)  a
 NestedSuccess :: EvalNestedSuccess s xs a
                   -> EvalSuccess s (NestedTag xs)  a

decoupleSuccess :: EvalSuccess s t a -> (s a -> EvalSuccess s t a,s a)
decoupleSuccess (LinearSuccess (ra,sa)) = (\sa'->LinearSuccess (ra,sa'),sa)
decoupleSuccess (StackSuccess  (ra,sa)) = (\sa'->StackSuccess  (ra,sa'),sa)
decoupleSuccess (NestedSuccess x) = undefined

successMapState :: (s1 a -> s2 a) -> EvalSuccess s1 tag a -> EvalSuccess s2 tag a 
successMapState f (LinearSuccess (ra,s)) = LinearSuccess (ra,f s)
successMapState f (StackSuccess  (ra,s)) = StackSuccess (ra,f s)
successMapState f (NestedSuccess q) = undefined 

successValueMap :: (a -> a) -> EvalSuccess s tag a -> EvalSuccess s tag a 
successValueMap f (LinearSuccess (ra,s)) = LinearSuccess (fmap f ra,s)
successValueMap f (StackSuccess  (ra,s)) = StackSuccess (fmap f ra,s)
successValueMap f (NestedSuccess q) = undefined 


type family EvalNestedSuccess (s :: * -> *) (xs :: Nonempty BaseTag) (a :: *) = d | d -> s xs a where
-- EvalNestedSuccess s xs a = CSum1 (CSumNestedF s) (Map1 (EvalBasecaseNestedSym1 s) (Tail1' (Tails1 xs))) a
 EvalNestedSuccess s xs a = CSum1 (CSumNestedF s) (Map1 (EvalBasecaseNestedSym1 s) (Tails1 xs)) a -- error here, should be tail of this, but thats not injective...

data EvalBasecaseNestedSym1 :: (* -> *) -> (Nonempty BaseTag) ~> (* -> *)
type instance Apply (EvalBasecaseNestedSym1 s) xs = EvalBasecaseNested s xs

class EvalBasecaseNested_class (xs :: Nonempty BaseTag) where
 type EvalBasecaseNested (s :: * -> *) xs = (nest :: (* -> *)) | nest -> xs s -- = (ys :: ZNonempty fs *) | ys -> xs s -- BaseTag

instance EvalBasecaseNested_class (End x) where
 type EvalBasecaseNested s (End x) = Nesting1 (End (EvalSuccess s x))

instance EvalBasecaseNested_class (x:|xs) where
 type EvalBasecaseNested s (x :| xs) = Nesting1 (EvalSuccess s x :| Map1 (TyCon1 EvalFail) xs)

-- Container 

data BaseTagOfSym0 :: (* -> *) ~> BaseTag
type instance Apply BaseTagOfSym0 f = BaseTagOf f

class (Transformation (BaseOf f),Functor f) => Container f where 
 type BaseTagOf f = (b:: BaseTag) | b -> f 

type family BaseOf (f :: * -> *) :: * -> (* -> *) -> * where
 BaseOf f = Base (BaseTagOf f) 

--type BaseOf' f a = Base (BaseTagOf f) a (f a)

type EvalFailOf f = EvalFail (BaseTagOf f)

instance Container [] where
 type BaseTagOf [] = StackTag Identity

instance Container Nonempty where
 type BaseTagOf Nonempty = LinearTag Identity

-- hylo

hylo :: Functor f => (a -> f a) -> (f b -> b) -> a -> b
hylo stateF act s = act $ fmap (hylo stateF act) (stateF s) 


hyloTransformation :: forall t f g a.  Transformation t => (f a -> t a f) -> (t a g -> g a) -> f a -> g a
hyloTransformation stateF act s = act $ transform ((hyloTransformation @t @f @g @a) stateF act) (stateF s) 

-- Unfolding

class Container f => Unfolding f where
 unfoldingr :: (x ~ (BaseOf f), Transformation x) => State x a s -> s a -> f a
 default unfoldingr :: (x ~ (BaseOf f), Transformation x,Set f) => State x a s -> s a -> f a
 unfoldingr sf s = hyloTransformation sf set s 

instance Unfolding []
instance Unfolding Nonempty

-- Set

type CoState x a s = x a s -> s a

type CoStateOf f a = CoState (BaseOf f) a f

class Unfolding f => Set f where
 set :: CoStateOf f a

instance Set [] where
 set (Fail _) = []  
 set (Success (StackSuccess (Identity x,xs))) = x:xs

instance Set Nonempty where
 set (Fail (LinearFail (Identity a))) = End a  
 set (Success (LinearSuccess (Identity x,xs))) = x:|xs

instance Container (Nesting1 fs) where
 type BaseTagOf (Nesting1 fs) = NestedTag (Map1 BaseTagOfSym0 fs) 

-- perfect use for Has / Empty class!
class CSumNestedF s f where
 cSumNestedF :: f a -> s a
-- this is the constraint that the values of the sum have to satisfy, that is, they need to be able to be turned into `s a'

-- wtf!?
instance (Set (Nesting1 xs),EvalSuccess (Nesting1 xs) (NestedTag (Map1 BaseTagOfSym0 xs)) ~ ys) => CSumNestedF (Nesting1 xs) (ys) where
 cSumNestedF x = let (f,s) = decoupleSuccess x in insert (set . Success . f) s

instance (Get f,Set f) => Set (Nesting1 (End f)) where
 set (Fail (NestedFail (Subject1 a))) = Subject1 $ set $ Fail a
 set (Success (NestedSuccess x)) = mapCSum1 cSumNestedF  x

instance (Get f,Set f,Set (Nesting1 fs)) => Set (Nesting1 (f :| fs)) where 
 set (Fail (NestedFail (Nest1 a))) = Nest1 $ fmap (set . Fail . NestedFail) $ set $ Fail a
 set (Success (NestedSuccess x)) = mapCSum1 cSumNestedF  x

instance Set (Nesting1 xs) => Unfolding (Nesting1 xs) 

-- Folding

class Container f => Folding f where
 foldingr :: (x ~ (BaseOf f), Transformation x) => CoState x a b -> f a -> b a
 default foldingr :: (x ~ (BaseOf f), Transformation x,Get f)  => CoState x a b -> f a -> b a
 foldingr action xs = hyloTransformation get action xs 

instance Folding []
instance Folding Nonempty
	
-- Get

type State   x a s = s a -> x a s

type StateOf f a = State (BaseOf f) a f

class Folding f => Get f where
 get :: StateOf f a

instance Get [] where
 get [] = Fail StackFail
 get (x:xs) = Success (StackSuccess (Identity x,xs))

instance Get Nonempty where
 get (End a) = Fail (LinearFail (Identity a))
 get (x:|xs) = Success (LinearSuccess (Identity x,xs))

instance (Get f,Set f) => Get (Nesting1 (End f)) where
 get (Subject1 xs) = get
{-
 set (Fail (NestedFail (Subject1 a))) = Subject1 $ set $ Fail a
 set (Success (NestedSuccess x)) = mapCSum1 cSumNestedF  x
-}

instance (Get f,Set f,Get (Nesting1 fs),Set (Nesting1 fs)) => Get (Nesting1 (f :| fs)) where 
{-
 set (Fail (NestedFail (Nest1 a))) = Nest1 $ fmap (set . Fail . NestedFail) $ set $ Fail a
 set (Success (NestedSuccess x)) = mapCSum1 cSumNestedF  x
-}

instance Get (Nesting1 fs) => Folding (Nesting1 fs)

{-
-- shit this requires the hierarch that stacks are linear and linears are streams
pattern  (:::) :: Container f => a -> f a -> f a
pattern x ::: xs <- (get0 -> (x,xs)) 
 where  x ::: xs =   set0    (x,xs) 
-}

test xs = hyloTransformation get set xs == xs

test1 = test [1 :: Int,2,3]
test2 = test ((1::Int) :| (2 :| (End 3)))
test3 = test (Nest1 [Subject1 [1::Int],Subject1 [2,3]])

data (Get f,Set f) => Zipper f a = Zipper [a] (f a) deriving Eq


--toZipper = Zipper []

forwards = undefined

backwards = undefined

