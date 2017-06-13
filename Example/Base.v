Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import GDTC.

Section DepthSize.

  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Context {PFun_E : PFunctor E}.
  Context {spf_E : SPF E}.
  Definition Exp := Fix E.

  (** Depth **)

  Definition depthOfR : Set := nat.
  Inductive DepthOfName : Set := depthofname.
  Context {DepthOf_E : forall R, FAlgebra DepthOfName R nat E}.
  Definition depthOf := fold_ (f_algebra DepthOfName id).

  (** Size **)

  Definition sizeOfR : Set := nat.
  Inductive SizeOfName : Set := sizeofname.
  Context {SizeOf_E : forall R, FAlgebra SizeOfName R nat E}.
  Definition sizeOf := fold_ (f_algebra SizeOfName id).

  (** DepthSize *)
  Definition DepthSizeP (e : Exp) : Prop :=
    depthOf e < sizeOf e.

  Context {depthSizePAlg : FPAlgebra DepthSizeP in_t}.
  Lemma depthSize : forall (e : Exp), DepthSizeP e.
  Proof. apply Ind. Qed.

End DepthSize.
