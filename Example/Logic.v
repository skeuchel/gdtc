Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
Require Import FJ_tactics.
Require Import Coq.Lists.List.
Require Import Containers.
Require Import Functors.
Require Import Polynomial.
Require Import Base.

Section Logic.

  Inductive Logic (a : Set) : Set :=
  | BLit : bool -> Logic a
  | If : a -> a -> a -> Logic a.

  Global Instance Logic_Iso : Iso Logic (K bool :+: Id :*: Id :*: Id) :=
    {| fromIso := fun A x => match x with
                               | BLit b => inl b
                               | If x y z => inr (x,(y,z))
                             end;
       toIso   := fun A x => match x with
                               | inl b => BLit _ b
                               | inr (x,(y,z)) => If _ x y z
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [n|[x [y z]]]; reflexivity.
  Defined.

  Global Instance Logic_Container : Container Logic :=
    ContainerIso Logic_Iso.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Let Exp := Fix F.
  Context {Sub_Logic_F : Logic :<: F}.

  (* Constructor. *)
  Definition blit (b : bool) : Exp := inject Logic F (BLit _ b).
  Definition cond (i t e : Exp) : Exp :=  inject Logic F (If _ i t e).

  (* Induction Principles for Logic. *)
  Definition ind_alg_Logic
    (P : Fix F -> Prop)
    (Hblit : forall b, P (blit b))
    (Hcond : forall i t e, P i -> P t -> P e -> P (cond i t e))
    : PAlgebra (inject Logic F) P :=
    fun xs =>
      match xs return (All P xs -> P (inject Logic F xs)) with
      | BLit b => fun Axs => Hblit b
      | If i t e => fun Axs =>
        Hcond i t e (Axs (inl _ tt)) (Axs (inr _ (inl _ tt))) (Axs (inr _ (inr _ tt)))
        (* | Add m n => fun Axs => Hadd m n (Axs PAdd1) (Axs PAdd2) *)
      end.

End Logic.

Section Depth.

  Definition Logic_depthOf (R : Set) (rec : R -> depthOfR)
    (e : Logic R) : depthOfR :=
    match e with
      | BLit b   => 0
      | If i t e => 1 + max (rec i) (max (rec t) (rec e))
    end.

  Global Instance MAlgebra_depthOf_Logic T :
    FAlgebra DepthOfName T depthOfR Logic :=
    {| f_algebra := Logic_depthOf T |}.

End Depth.

Section Size.

  Definition Logic_sizeOf (R : Set) (rec : R -> sizeOfR)
    (e : Logic R) : sizeOfR :=
    match e with
      | BLit b   => 1
      | If i t e => 1 + rec i + rec t + rec e
    end.

  Global Instance MAlgebra_sizeOf_Logic T :
    FAlgebra SizeOfName T sizeOfR Logic :=
    {| f_algebra := Logic_sizeOf T |}.

End Size.

Section DepthSize.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Context {Sub_Logic_F : Logic :<: F}.
  Context {WF_Sub_Logic_F : WF_Functor _ _ Sub_Logic_F}.

  Context {depthOf_F : forall R, FAlgebra DepthOfName R nat F}.
  Context {WF_depthOf_F : forall R, WF_FAlgebra DepthOfName _ _ Logic F
    (MAlgebra_depthOf_Logic _) (depthOf_F R)}.

  Context {sizeOf_F : forall R, FAlgebra SizeOfName R nat F}.
  Context {WF_sizeOf_F : forall R, WF_FAlgebra SizeOfName _ _ Logic F
    (MAlgebra_sizeOf_Logic _) (sizeOf_F R)}.

  Context {depthSizePAlg : FPAlgebra (DepthSizeP F) in_t}.

  Ltac logicAlgs :=
    repeat
      match goal with
      | |- context[depthOf ?F (inject ?A ?F ?x)] =>
        replace (depthOf F (inject Logic F x)) with
        (f_algebra DepthOfName id (inj (fmap (depthOf F) x)))
          by (unfold inject, depthOf; rewrite fold_computation, wf_functor; auto)
      | |- context[sizeOf ?F (inject ?A ?F ?x)] =>
        replace (sizeOf F (inject Logic F x)) with
        (f_algebra SizeOfName id (inj (fmap (sizeOf F) x)))
          by (unfold inject, sizeOf; rewrite fold_computation, wf_functor; auto)
      end; simpl;
    rewrite ?(@wf_mixin nat nat Logic F _ _ _ (WF_depthOf_F nat)); simpl;
    rewrite ?(@wf_mixin nat nat Logic F _ _ _ (WF_sizeOf_F nat)); simpl.

  Arguments id {A} x /.

  Global Instance Logic_DepthSize : FPAlgebra (DepthSizeP F) (inject Logic F).
  Proof.
    constructor; unfold Algebra; intros.
    apply ind_alg_Logic; unfold DepthSizeP, blit, cond; simpl; intros.
    - logicAlgs; omega.
    - logicAlgs.
      destruct (Max.max_spec (depthOf F i) (max (depthOf F t) (depthOf F e)))
        as [[_ Heq]|[_ Heq]]; rewrite Heq; clear Heq; try omega.
      destruct (Max.max_spec (depthOf F t) (depthOf F e))
        as [[_ Heq]|[_ Heq]]; rewrite Heq; clear Heq; try omega.
  Qed.

End DepthSize.
