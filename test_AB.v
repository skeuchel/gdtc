Require Import String.
Require Import Names.
Require Import Arith.
Require Import Bool.
Require Import Functors.
(* Require Import MonadLib. *)

Open Scope string_scope.

Section Type_Test_Section. 
  (* Type Testing, of course. *)
  Definition D := AType :+: BType.

  Definition tex1' : DType D := tnat' _. (* Nat *)
  Definition tex1 := proj1_sig tex1'.
  Definition tex2' : DType D := tbool' _. (* Bool *)
  Definition tex2 := proj1_sig tex2'.

  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat.").
  Eval compute in (eq_DType D tex1 tex1').
  Eval compute in ("Evaluating 'tbool == tbool' as an 'TBool.").
  Eval compute in (eq_DType D tex2 tex2').
  Eval compute in ("Evaluating 'tbool == tnat' as an 'TBool.").
  Eval compute in (eq_DType D tex2 tex1').

End Type_Test_Section.

Section Test_Section.

  Definition E := Arith :+: Bool.

  Definition ex_1 : Names.Exp E :=
    (add' _ (lit' _ 1) (lit' _ 2)).
  Definition ex_2 : Names.Exp E := 
    (add' _ (lit' _ 5) (lit' _ 0)).
  Definition ex_3 : Names.Exp E := 
    (cond' _ (blit' _ true) ex_1 ex_2).
  Definition ex_4 : Names.Exp E := 
    (cond' _ (blit' _ false) ex_1 ex_2).

  Definition test_typeof e := 
    match (typeof D E e) with 
      | Some t1 => DTypePrint _ (proj1_sig t1)
      | None => "Type Error!"
    end.

  Eval compute in ("The type of '1 + 2' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_1)).
  Eval compute in ("The type of '145 + 2346' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_2)).
  Eval compute in ("The type of 'true' should be tbool.").
  Eval compute in (test_typeof (blit _ true)).
  Eval compute in ("The type of 'if true then (1 + 2) else (5 + 0)' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_3)).
  Eval compute in ("The type of 'if false then (1 + 2) else (5 + 0)' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_4)).
    
  Eval compute in (ExpPrint E (proj1_sig ex_1)).
  Eval compute in (ExpPrint E (proj1_sig ex_2)).
  Eval compute in (ExpPrint E (proj1_sig ex_3)).
  Eval compute in (ExpPrint E (proj1_sig ex_4)).

  Definition V := StuckValue :+: BotValue :+: NatValue :+: BoolValue.

  Eval compute in ("Evaluating '1 + 2'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_1) nil))).
  Eval compute in ("Evaluating '5 + 0'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_2) nil))).
  Eval compute in ("Evaluating 'if true then (1 + 2) else (5 + 0)'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_3) nil))).
  Eval compute in ("Evaluating 'if false then (1 + 2) else (5 + 0)'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_4) nil))).

  Definition WFV := (WFValue_Bot D V) ::+:: (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Instance typeof_alg : forall T, FAlgebra TypeofName T (typeofR D) E.
    intros; eauto 200 with typeclass_instances.
  Defined.

  Instance eval_alg : forall T, FAlgebra EvalName T (evalR V) E.
    eauto 500 with typeclass_instances.
  Defined.

  Lemma Soundness_Alg typeof_rec eval_rec : 
    PAlgebra eval_Soundness_alg_Name (sig (UP'_P2 (eval_alg_Soundness_P D V E WFV unit
      (fun _ _ => True) E (Functor_Plus Arith Bool) tt typeof_rec eval_rec
      f_algebra f_algebra))) E.
    eauto 100 with typeclass_instances.
  Defined.
    
  Lemma soundness : forall (e : Exp E),
    forall T, typeof D E (proj1_sig e) = Some T -> 
      WFValueC D V WFV (eval V E (proj1_sig e) nil) T.
  Proof.    
    intro; apply eval_Soundness with (eval_Soundness_alg_F := Soundness_Alg);
      eauto 550 with typeclass_instances.
  Qed.
 
  Eval compute in ("Type Soundness for Arith :+: Bool Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
