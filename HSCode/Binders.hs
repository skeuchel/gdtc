{-# LINE 1 "Binders.lhs" #-}

  {-# OPTIONS -XRankNTypes -XLiberalTypeSynonyms -XImpredicativeTypes -XDeriveFunctor -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances -XFlexibleContexts #-}
  {-# LANGUAGE ScopedTypeVariables #-}

  module Binders where

  import Extensibility hiding (Value, Fix)
  import Subtyping hiding (Stuck)

  data Lambda v r =
      Var v
   |  App r r
   |  Lam (v -> r)

   deriving Functor
 
  var :: (Lambda v :<: f) => v -> MFix f
  var v = inject (Var v)
 
  app :: forall v f. (Lambda v :<: f) => MFix f -> MFix f -> MFix f
  app e1 e2 = inject ((App :: MFix f -> MFix f -> Lambda v (MFix f)) e1 e2)
 
  lam :: forall v f . (Lambda v :<: f) => (v -> MFix f) -> MFix f
  lam f = inject ((Lam :: (v -> MFix f) -> Lambda v (MFix f)) f)

  type Env v = [v]

  data ClosureF f a = Closure1 (MFix f) (Env a)
 
  closure ::  (ClosureF f :<: r) => 
              MFix f -> Env (MFix r) -> MFix r
  closure mf e = inject (Closure1 mf e)

  class Eval f where
    evalAlg :: Mendler f (Value f)
 
  data Value f = 
      Stuck
   |  Constant Nat
   |  Closure (MFix f) (Env (Value f)) 

  data ClosureF2 f v = Closure2 (v -> MFix f)
  data ClosureF3 v = Closure3 (v -> v)

  closure2 :: (ClosureF2 f :<: r) => (MFix r -> MFix f) -> MFix r
  closure2 f = inject (Closure2 f)
 
  closure3 :: forall r . (ClosureF3 :<: r) => (MFix r -> MFix r) -> MFix r
  closure3 f = inject ((Closure3 :: (MFix r -> MFix r) -> ClosureF3 (MFix r)) f)

  type Mixin t f a = (t -> a) -> f t -> a

  evalLambda :: Mixin (MFix f) (Lambda Nat) (Env (Value f) -> Value f)
  evalLambda rec exp env = 
    case exp of
      Var index  
        -> env !! index
      Lam f      
        -> Closure (f (length env)) env
      App e1 e2  
        -> case rec e1 env of
             Closure e1' env'  -> rec e1' (rec e2 env : env')
             _                 -> Stuck 

  evalLambda3 :: (ClosureF2 f :<: r, StuckF :<: r, Functor r) => Mixin (MFix f) (Lambda (MFix r)) (MFix r)
  evalLambda3 rec exp = 
    case exp of
      Var v      -> v
      Lam f      -> closure2 f
      App e1 e2  -> 
        case project (rec e1) of
             Just (Closure2 f)  -> rec (f (rec e2))
             _                  -> stuck

  evalLambda4 :: (ClosureF3 :<: r, StuckF :<: r, Functor r) => Mixin (MFix f) (Lambda (MFix r)) (MFix r)
  evalLambda4 rec exp = 
    case exp of
      Var v      -> v
      Lam f      -> closure3 (\v -> rec (f v))
      App e1 e2  -> 
        case project (rec e1) of
             Just (Closure3 f)  -> f (rec e2)
             _                  -> stuck

  evalLambda2 :: forall f r . (ClosureF f :<: r, StuckF :<: r, Functor r) 
              => Mixin  (MFix f) (Lambda Nat) 
                        (Env (MFix r) -> MFix r)
  evalLambda2 rec exp env = 
    case exp of
      Var index  
        -> lookup env index
      Lam f      
        -> closure (f (length env)) env
      App e1 e2  
        -> case project $ rec e1 env of
             Just (Closure1 e1' env')  -> rec e1' (cons (rec e2 env) env')
             _                         -> stuck
      where lookup :: Env (MFix r) -> Nat -> MFix r
            lookup (x:_)  0  = x
            lookup (_:xs) n  = lookup xs (n-1)
            cons   :: MFix r -> Env (MFix r) -> Env (MFix r)
            cons v env       = ((:) :: MFix r -> Env (MFix r) -> Env (MFix r)) v env

  class MixEval f g r where
     malgebra :: Mixin (MFix f) g (Env (MFix r) -> MFix r)
 
  instance  (StuckF :<: r, ClosureF f :<: r, Functor r) => 
            MixEval f (Lambda Nat) r where
     malgebra = evalLambda2

  type Res r = Env (MFix r) -> MFix r

  eval' :: forall f r. (Functor f, StuckF :<: r, MixEval f f r) => MFix f -> (forall a. Mendler r a -> a)
  eval' e = exp1 where
     exp1 = ((app3 (app2 (app1 (boundedFix 1000) def) p) e) nil) 
     app1 :: forall b. (Res r -> b) -> Res r -> b
     app1 f x = f x
     app2 :: forall b. (Mixin (MFix f) f (Res r) -> b) -> Mixin (MFix f) f (Res r) -> b
     app2 f x = f x
     app3 :: forall b. (MFix f -> b) -> MFix f -> b
     app3 f x = f x
     p ::  Mixin (MFix f) f (Res r)
     p = malgebra 
     def :: Res r
     def = \_ -> stuck
     nil :: Env (MFix r)
     nil = []

  boundedFix ::  forall f a. Functor f => Nat  -> a -> 
                 Mixin (MFix f) f a -> MFix f -> a
  boundedFix n def alg e =
    case n of
      0    -> def
      m    -> alg (boundedFix (m-1) def alg) (out_t e)

  mendlerToMixin :: Mendler f a -> Mixin (MFix g) f a
  mendlerToMixin alg = alg

  class Eval3 f v where -- Supposed to come from Section 2!
    evalAlgebra :: Mendler f (Value v)

  {-
  (<@>) :: Mixin e f r -> Mixin e g r -> Mixin e (f :+: g) r
  evalf <@> evalg = \eval e -> 
    case e of 
      Inl x -> evalf eval x
      Inr y -> evalg eval y
  -}

  class Eval2 f g a where 
     algebra :: Mixin (MFix f) g a -- should be Mixin r g a
 
  instance Eval2 f (Lambda Nat) 
     (Env (Value f) -> Value f) where
     algebra = evalLambda 

  instance (Eval2 h f a, Eval2 h g a) => 
     Eval2 h (f :+: g) a where
     algebra eval (Inl x) = algebra eval x
     algebra eval (Inr y) = algebra eval y

  type IntLambda = Lambda Nat :+: ArithF
