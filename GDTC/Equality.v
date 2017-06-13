Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Import Functors.
Require Import Containers.
Require Import Polynomial.

Section Equality.

  Class Eq (A : Set) :=
    { eq                     :  A -> A -> bool;
      eq_propositional_true  : forall (x y : A), eq x y = true  -> x = y;
      eq_propositional_false : forall (x y : A), eq x y = false -> x <> y
    }.

  Variable c : Code.

  Definition EQA := FixP c -> bool.
  Definition EQB (d : Code) := ExtP (FixP c) d -> bool.

  (*
  Fixpoint eqalg (d : Code) (x : ExtP EQA d) : EQB d.
  Proof.
    destruct x; intro y.
    apply true.
    inversion y.
    apply (e H).
    inversion y; subst.
    apply (eqalg _ _ H0).
    unfold
  *)

  Definition eqf (eq : EQB c) : EQA :=
    fun x => match x with
               | fixp e => eq e
             end.
  Definition equ (x : ExtP (FixP c) U) : bool := true.
  Definition eqi (f : EQA) : EQB I :=
    fun x => match x with
               | ei x => f x
               | _     => false
             end.
  Definition eql (c1 c2 : Code) (eq : EQB c1) : EQB (C c1 c2).
    intro x; inversion x; subst.
    apply (eq H0).
    apply false.
  Defined.
  Definition eqr (c1 c2 : Code) (eq : EQB c2) : EQB (C c1 c2).
    intro x; inversion x; subst.
    apply false.
    apply (eq H0).
  Defined.
  Definition eqp (c1 c2 : Code) (eq1 : EQB c1) (eq2 : EQB c2) : EQB (P c1 c2).
    intro x; inversion x; subst.
    apply (andb (eq1 H1) (eq2 H2)).
  Defined.

  Definition eqfix : FixP c -> FixP c -> bool :=
    fixpfold2 c EQA EQB eqf equ eqi eql eqr eqp.
  Definition eqext : forall d, ExtP (FixP c) d -> ExtP (FixP c) d -> bool :=
    extpfold2 c EQA EQB eqf equ eqi eql eqr eqp.

  Lemma eqfix_propositional_true :
    forall u v, eqfix u v = true -> u = v.
  Proof.
    apply (fixp_ind c
            (fun u   => forall v, eqfix u v = true -> u = v)
            (fun d u => forall v, eqext d u v = true -> u = v));
      intros;
      dependent destruction v;
      try (f_equal; apply (H _ H0));
      try discriminate.
    (* ep *)
    unfold eqext in H1.
    unfold extpfold2 in H1.
    simpl in H1.
    apply andb_true_iff in H1.
    destruct H1.
    f_equal.
    apply (H _ H1).
    apply (H0 _ H2).
  Qed.

  Lemma eqfix_propositional_false :
    forall u v, eqfix u v = false -> u <> v.
  Proof.
    apply (fixp_ind c
            (fun u   => forall v, eqfix u v = false -> u <> v)
            (fun d u => forall v, eqext d u v = false -> u <> v));
      intros;
      dependent destruction v;
      try discriminate;
      intro Heq; inversion Heq; subst.
    apply (H e); auto.
    apply (H f); auto.
    apply inj_pairT2 in H2.
    apply (H _ H0); auto.
    apply inj_pairT2 in H2.
    apply (H _ H0); auto.
    apply inj_pairT2 in H3.
    apply inj_pairT2 in H4.
    subst.
    unfold eqext in H1.
    unfold extpfold2 in H1.
    simpl in H1.
    apply andb_false_iff in H1.
    destruct H1.
    apply (H _ H1); auto.
    apply (H0 _ H1) ; auto.
  Qed.

  Global Instance Eq_FixP : Eq (FixP c) :=
    {| eq := eqfix;
       eq_propositional_true := eqfix_propositional_true;
       eq_propositional_false := eqfix_propositional_false |}.

End Equality.

Section Container.
  Variable (F : Set -> Set).
  Context {poly_F : Polynomial F}.
  Existing Instance PolynomialContainer.

  Global Instance Eq_Fix : Eq (Fix F) :=
    {| eq := fun x y => eq (toFixP _ x) (toFixP _ y) |}.
  Proof.
    intros; simpl.
    apply eq_propositional_true in H.
    apply f_equal with (f := fromFixP PCode) in H.
    repeat rewrite fromFixP_toFixP_inverse in H.
    auto.
    intros.
    apply eq_propositional_false in H.
    intro.
    apply H.
    f_equal.
    auto.
  Defined.

End Container.
