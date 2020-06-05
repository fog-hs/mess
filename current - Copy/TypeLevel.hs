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

module TypeLevel where

import TyFun


--

data Proxy (a :: k) = Proxy



-- Const

data ConstSym0 :: a ~> b ~> a 
type instance Apply ConstSym0 a = ConstSym1 a 

data ConstSym1 :: a -> b ~> a 
type instance Apply (ConstSym1 a) b = Const a b

type family Const (x :: a) (y :: b) = (c :: a) where
 Const x y = x
