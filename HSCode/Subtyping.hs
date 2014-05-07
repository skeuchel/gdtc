{-# LINE 1 "Subtyping.lhs" #-}
#line 1 "Subtyping.lhs"

  {-# OPTIONS -XRankNTypes -XImpredicativeTypes -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XOverlappingInstances -XFlexibleContexts  -XUndecidableInstances #-}

  {-# LANGUAGE ScopedTypeVariables #-}

  module Subtyping where

  import Extensibility hiding (lit, I, B)

  data (:+:) f g a = Inl (f a) | Inr (g a)

  infixr 7 :+:

  class Eval f where
    evalAlg :: Mendler f Value

  instance (Eval f, Eval g) => Eval (f :+: g) where
    evalAlg eval (Inl fexp)  = evalAlg eval fexp
    evalAlg eval (Inr gexp)  = evalAlg eval gexp 

  eval2 :: Eval f => MFix f -> Value
  eval2 = mfold evalAlg

  class f :<: g where
    inj      :: f a -> g a 
    prj      :: g a -> Maybe (f a)
 
  instance f :<: (f :+: h) where 
    inj fa        = Inl fa
    prj (Inl ga)  = Just ga
    prj (Inr ha)  = Nothing
 
  instance (f :<: h) => f :<: (g :+: h) where 
    inj fa        = Inr (inj fa)
    prj (Inl ga)  = Nothing 
    prj (Inr ha)  = prj ha
  
  instance f :<: f where
    inj fa = fa
    prj fa = Just fa

  in_t :: f (MFix f) -> MFix f
  in_t fexp = \alg -> alg (mfold alg) fexp

  in_t1 :: Functor f => f (Fix f) -> Fix f
  in_t1 fexp = \alg -> alg (fmap (fold alg) fexp)

  inject :: (g :<: f) => g (MFix f) -> MFix f 
  inject gexp = in_t (inj gexp)
 
  lit :: (ArithF :<: f) => Nat -> MFix f
  lit n = inject (Lit n)
 
  blit :: (IfF :<: f) => Bool -> MFix f
  blit b = inject (BLit b)

  cond  :: forall f. (IfF :<: f) => MFix f -> MFix f -> MFix f -> MFix f
  cond c e1 e2 alg = inject ((If :: (MFix f -> MFix f -> MFix f -> IfF (MFix f)))
                                c e1 e2) alg

  out_t :: forall f. Functor f => MFix f -> f (MFix f)
  out_t exp = mfold (\rec fr -> (fmap :: ((r -> MFix f) -> f r -> f (MFix f))) (\r -> in_t (rec r)) fr) exp
  {-
    where  
      g :: (r -> f (Fix f)) -> f r -> f (Fix f)
      g ffexp = (fmap :: ((f (Fix f) -> Fix f) -> f (f (Fix f)) -> f (Fix f))) 
                  in_t
                  ffexp
  -}

  project :: (g :<: f, Functor f) => 
          MFix f -> Maybe (g (MFix f))
  project exp = prj (out_t exp)
 
  isLit :: (ArithF :<: f, Functor f) => MFix f -> Maybe Nat
  isLit exp = case project exp of
      Just (Lit n)  -> Just n
      Nothing       -> Nothing

  data NValF a   = I Nat
  data BValF a   = B Bool
  data StuckF a  = Stuck
 
  vi  :: (NValF :<: r) => Nat -> MFix r
  vi n = inject (I n)
 
  vb :: (BValF :<: r) => Bool -> MFix r
  vb b = inject (B b)
  
  stuck :: (StuckF :<: r) => MFix r
  stuck = inject Stuck

  class EEval f r where
    eevalAlg :: Mendler f (MFix r)

  instance (StuckF :<: r, NValF :<: r, Functor r) => 
    EEval ArithF r where
      eevalAlg eval (Lit n)      = vi n
      eevalAlg eval (Add e1 e2)  =
        case (project (eval e1), project (eval e2)) of
          (Just (I n1), (Just (I n2)))  ->  vi (n1 + n2)
          _                             ->  stuck

