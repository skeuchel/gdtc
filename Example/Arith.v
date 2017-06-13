Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
Require Import FJ_tactics.
Require Import Coq.Lists.List.
Require Import Containers.
Require Import Functors.
Require Import Polynomial.
Require Import Base.

Section Arith.

  Inductive Arith (a : Set) : Set :=
  | Lit (n : nat)
  | Add (a1 a2 : a).

  (* Global Instance FunctorArith : Functor Arith := *)
  (*   {| fmap := fun a b f e => match e with *)
  (*                             | Lit n => Lit b n *)
  (*                             | Add a1 a2 => Add b (f a1) (f a2) *)
  (*                             end *)
  (*   |}. *)
  (* Proof. *)
  (*   - now destruct a. *)
  (*   - now destruct a. *)
  (* Defined. *)

  (* Inductive AllArith (a : Set) (p : a -> Prop) : Arith a -> Prop := *)
  (* | ALit {n : nat} : AllArith a p (Lit a n) *)
  (* | AAdd {a1 a2 : a} : p a1 -> p a2 -> AllArith a p (Add a a1 a2). *)

  (* Global Instance PFunctorArith : PFunctor Arith := *)
  (*   {| All := AllArith |}. *)
  (* Proof. *)
  (*   intros ? ? ? ? xs; destruct xs; split; inversion 1; now constructor. *)
  (* Defined. *)

  Global Instance Arith_Iso : Iso Arith (K nat :+: Id :*: Id) :=
    {| fromIso := fun A x => match x with
                               | Lit n => inl n
                               | Add x y => inr (x,y)
                             end;
       toIso   := fun A x => match x with
                               | inl n => Lit _ n
                               | inr (x,y) => Add _ x y
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [n|[x y]]; reflexivity.
  Defined.

  Global Instance Arith_Container : Container Arith :=
    ContainerIso Arith_Iso.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Let Exp := Fix F.
  Context {Sub_Arith_F : Arith :<: F}.

  (* Constructor + Universal Property. *)
  Definition lit (n : nat) : Exp := inject Arith F (Lit _ n).
  Definition add (m n : Exp) : Exp :=  inject Arith F (Add _ m n).

  (* (* Induction Principles for Arith. *) *)
  (* Definition ind_alg_Arith *)
  (*   (P : Fix F -> Prop) *)
  (*   (Hlit : forall n, P (lit n)) *)
  (*   (Hadd : forall m n, P m -> P n -> P (add m n)) *)
  (*   : PAlgebra (inject Arith F) P := *)
  (*   fun xs Axs => *)
  (*     match Axs in AllArith _ _ xs *)
  (*           return P (inject Arith F xs) with *)
  (*     | ALit n           => Hlit n *)
  (*     | AAdd a1 a2 p1 p2 => Hadd a1 a2 p1 p2 *)
  (*     end. *)

  (* Induction Principles for Arith. *)
  Definition ind_alg_Arith
    (P : Fix F -> Prop)
    (Hlit : forall n, P (lit n))
    (Hadd : forall m n, P m -> P n -> P (add m n))
      : PAlgebra (inject Arith F) P :=
    fun xs => match xs return (All P xs -> P (inject Arith F xs)) with
                | Lit n => fun Axs => Hlit n
                | Add m n => fun Axs => Hadd m n (Axs (inl _ tt)) (Axs (inr _ tt))
                (* | Add m n => fun Axs => Hadd m n (Axs PAdd1) (Axs PAdd2) *)
              end.

End Arith.

Section Depth.

  Definition Arith_depthOf (R : Set) (rec : R -> depthOfR)
    (e : Arith R) : depthOfR :=
    match e with
      | Lit n   => 0
      | Add m n => 1 + max (rec m) (rec n)
    end.

  Global Instance MAlgebra_depthOf_Arith T :
    FAlgebra DepthOfName T depthOfR Arith :=
    {| f_algebra := Arith_depthOf T |}.

End Depth.

Section Size.

  Definition Arith_sizeOf (R : Set) (rec : R -> sizeOfR)
    (e : Arith R) : sizeOfR :=
    match e with
      | Lit n   => 1
      | Add m n => 1 + rec m + rec n
    end.

  Global Instance MAlgebra_sizeOf_Arith T :
    FAlgebra SizeOfName T sizeOfR Arith :=
    {| f_algebra := Arith_sizeOf T |}.

End Size.

Section DepthSize.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Context {Sub_Arith_F : Arith :<: F}.
  Context {WF_Sub_Arith_F : WF_Functor _ _ Sub_Arith_F}.

  Context {depthOf_F : forall R, FAlgebra DepthOfName R nat F}.
  Context {WF_depthOf_F : forall R, WF_FAlgebra DepthOfName _ _ Arith F
    (MAlgebra_depthOf_Arith _) (depthOf_F R)}.

  Context {sizeOf_F : forall R, FAlgebra SizeOfName R nat F}.
  Context {WF_sizeOf_F : forall R, WF_FAlgebra SizeOfName _ _ Arith F
    (MAlgebra_sizeOf_Arith _) (sizeOf_F R)}.

  Context {depthSizePAlg : FPAlgebra (DepthSizeP F) in_t}.

  Ltac arithAlgs :=
    repeat
      match goal with
      | |- context[depthOf ?F (inject ?A ?F ?x)] =>
        replace (depthOf F (inject Arith F x)) with
        (f_algebra DepthOfName id (inj (fmap (depthOf F) x)))
          by (unfold inject, depthOf; rewrite fold_computation, wf_functor; auto)
      | |- context[sizeOf ?F (inject ?A ?F ?x)] =>
        replace (sizeOf F (inject Arith F x)) with
        (f_algebra SizeOfName id (inj (fmap (sizeOf F) x)))
          by (unfold inject, sizeOf; rewrite fold_computation, wf_functor; auto)
      end; simpl;
    rewrite ?(@wf_mixin nat nat Arith F _ _ _ (WF_depthOf_F nat)); simpl;
    rewrite ?(@wf_mixin nat nat Arith F _ _ _ (WF_sizeOf_F nat)); simpl.

  Arguments id {A} x /.

  Global Instance Arith_DepthSize : FPAlgebra (DepthSizeP F) (inject Arith F).
  Proof.
    constructor; unfold Algebra; intros.
    apply ind_alg_Arith; unfold DepthSizeP, lit, add; simpl; intros.
    - arithAlgs; omega.
    - arithAlgs.
      destruct (Max.max_spec (depthOf F m) (depthOf F n))
        as [[_ Heq]|[_ Heq]]; rewrite Heq; clear Heq; try omega.
  Qed.

End DepthSize.
