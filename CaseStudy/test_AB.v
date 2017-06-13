Require Import Coq.Strings.String.
Require Import GDTC.
Require Import CaseStudy.Names.
Require Import CaseStudy.Arith.
Require Import CaseStudy.Bool.

Open Scope string_scope.

Section Type_Test_Section.
  (* Type Testing, of course. *)
  Definition D := AType :+: BType.

  Global Instance Container_D : Container D :=
    PolynomialContainer D.

  Definition tex1 : DType D := tnat D. (* Nat *)
  Definition tex2 : DType D := tbool D. (* Bool *)

  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat.").
  Eval compute in (eq_DType D tex1 tex1).
  Eval compute in ("Evaluating 'tbool == tbool' as an 'TBool.").
  Eval compute in (eq_DType D tex2 tex2).
  Eval compute in ("Evaluating 'tbool == tnat' as an 'TBool.").
  Eval compute in (eq_DType D tex2 tex1).

End Type_Test_Section.

Section Test_Section.

  Definition E := Arith :+: Bool.
  Let Exp := Fix E.

  Global Instance Container_E : Container E.
    eauto with typeclass_instances.
  Defined.

  Definition ex_1 : Exp :=
    (add E (lit _ 1) (lit _ 2)).
  Definition ex_2 : Exp :=
    (add E (lit _ 5) (lit _ 0)).
  Definition ex_3 : Exp :=
    (cond E (blit _ true) ex_1 ex_2).
  Definition ex_4 : Exp :=
    (cond E (blit _ false) ex_1 ex_2).

  Definition test_typeof e :=
    match (typeof D E e) with
      | Some t1 => DTypePrint _ t1
      | None => "Type Error!"
    end.

  Eval compute in ("The type of '1 + 2' should be tnat.").
  Eval compute in (test_typeof ex_1).
  Eval compute in ("The type of '145 + 2346' should be tnat.").
  Eval compute in (test_typeof ex_2).
  Eval compute in ("The type of 'true' should be tbool.").
  Eval compute in (test_typeof (blit E true)).
  Eval compute in ("The type of 'if true then (1 + 2) else (5 + 0)' should be tnat.").
  Eval compute in (test_typeof ex_3).
  Eval compute in ("The type of 'if false then (1 + 2) else (5 + 0)' should be tnat.").
  Eval compute in (test_typeof ex_4).

  Eval compute in (ExpPrint E ex_1).
  Eval compute in (ExpPrint E ex_2).
  Eval compute in (ExpPrint E ex_3).
  Eval compute in (ExpPrint E ex_4).

  Definition V := StuckValue :+: BotValue :+: NatValue :+: BoolValue.

  Instance Container_V : Container V.
    eauto with typeclass_instances.
  Defined.

  Eval compute in ("Evaluating '1 + 2'").
  Eval compute in (ValuePrint V (eval V E ex_1 nil)).
  Eval compute in ("Evaluating '5 + 0'").
  Eval compute in (ValuePrint V (eval V E ex_2 nil)).
  Eval compute in ("Evaluating 'if true then (1 + 2) else (5 + 0)'").
  Eval compute in (ValuePrint V (eval V E ex_3 nil)).
  Eval compute in ("Evaluating 'if false then (1 + 2) else (5 + 0)'").
  Eval compute in (ValuePrint V (eval V E ex_4 nil)).

  Definition WFV := (WFValue_Bot D V) ::+:: (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Global Instance Container_WFV : IContainer WFV.
    eauto with typeclass_instances.
  Defined.

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D) E.
    intros; eauto 200 with typeclass_instances.
  Defined.

  Instance eval_alg : forall T, FAlgebra EvalName T (evalR V) E.
    eauto 500 with typeclass_instances.
  Defined.

  Lemma soundness : forall (e : Exp),
    forall T, typeof D E e = Some T ->
      WFValueC D V WFV (eval V E e nil) T.
  Proof.
    intro; apply eval_Soundness; eauto 150 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for Arith :+: Bool Proven!").

End Test_Section.
