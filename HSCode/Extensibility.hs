{-# LINE 1 "Extensibility.lhs" #-}
#line 1 "Extensibility.lhs"

  {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts #-}

  module Extensibility where

  data ArithF a = Lit Nat | Add a a

  instance Eq Value where
    (I x) == (I y) = x == y
    (B x) == (B y) = x == y

  data Value = I Int | B Bool 
 
  arithAlg :: Algebra ArithF Value
  arithAlg (Lit n)              = I n
  arithAlg (Add (I v1) (I v2))  = I (v1 + v2)

  eval :: Fix ArithF -> Value
  eval = fold arithAlg

  type Algebra f a = f a -> a

  type Fix f = forall a . Algebra f a -> a
 
  fold :: Algebra f a -> Fix f -> a
  fold alg fa = fa alg

  type Nat = Int

  lit :: Nat -> Fix ArithF
  lit n = \alg -> alg (Lit n)
 
  add :: Fix ArithF -> Fix ArithF -> Fix ArithF
  add e1 e2 = \alg -> alg (Add (fold alg e1) (fold alg e2))

  data IfF a  =  If a a a  -- functor   
              |  BLit Bool 
 
  ifEval :: Algebra IfF Value  
  ifEval (If v1 v2 v3)  = if (v1 == B True) then v2 else v3 
  ifEval (BLit b)       = B b

  type Mendler f a = forall r. (r -> a) -> f r -> a

  type MFix f = forall a . Mendler f a -> a
 
  mfold :: Mendler f a -> MFix f -> a
  mfold alg fa = fa alg

  -- in_t :: f (MFix f) -> MFix f 
  -- in_t fexp = \alg -> alg (mfold alg) fexp
 
  -- out_t :: Functor f => MFix f -> f (MFix f)
  -- out_t exp = mfold (\rec fr -> fmap (\r -> in_t (rec r)) fr) exp

  ifEval2 :: Mendler IfF Value
  ifEval2 eval (BLit b)       = B b
  ifEval2 eval (If e1 e2 e3)  = if (eval e1 == B True)  then  eval e2 
                                                        else  eval e3

