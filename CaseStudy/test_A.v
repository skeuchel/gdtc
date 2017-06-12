Require Import String.
Require Import FunctionalExtensionality.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.
Require Import CaseStudy.Names.
Require Import CaseStudy.Arith.

Open Scope string_scope.

Section Type_Test_Section.

  (* Type Testing, of course. *)
  Definition D := AType.

  Global Instance Container_D : Container D :=
    PolynomialContainer D.

  Definition tex1 : DType D := tnat D. (* Nat *)

  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat.").
  Eval compute in (eq_DType D tex1 tex1).

End Type_Test_Section.

Section Test_Section.

  Definition E := Arith.

  Definition ex_1 : Exp E :=
    (add _ (lit _ 1) (lit _ 2)).
  Definition ex_2  : Exp E :=
    (add _ (lit _ 5) (lit _ 0)).
  Definition ex_3  : Exp E :=
      (add _ ex_1 ex_2).

  Definition test_typeof (e : Exp E) :=
    match (typeof D E e) with
      | Some t1 => DTypePrint _ t1
      | None => "Type Error!"
    end.

  Eval compute in ("The type of '1 + 2' should be tnat.").
  Eval compute in (test_typeof ex_1).
  Eval compute in ("The type of '145 + 2346' should be tnat.").
  Eval compute in (test_typeof ex_2).
  Eval compute in ("The type of '(1 + 2) + (5 + 0)' should be tnat.").
  Eval compute in (test_typeof ex_3).

  Eval compute in (ExpPrint E ex_1).
  Eval compute in (ExpPrint E ex_2).
  Eval compute in (ExpPrint E ex_3).

  Definition V := StuckValue :+: BotValue :+: NatValue.

  Instance Container_V : Container V.
    eauto with typeclass_instances.
  Defined.

  Eval compute in ("Evaluating '1 + 2'").
  Eval compute in (ValuePrint V (eval V E ex_1 nil)).
  Eval compute in ("Evaluating '5 + 0'").
  Eval compute in (ValuePrint V (eval V E ex_2 nil)).
  Eval compute in ("Evaluating '(1 + 2) + (5 + 0)'").
  Eval compute in (ValuePrint V (eval V E ex_3 nil)).

  Definition WFV := (WFValue_VI D V).

  Lemma soundness : forall (e : Exp E),
    forall T, typeof D E e = Some T ->
      WFValueC D V WFV (eval V E e nil) T.
  Proof.
    intro; apply eval_Soundness; eauto 100 with typeclass_instances.
  Defined.

  Eval compute in ("Type Soundness for Arith Proven!").

End Test_Section.
