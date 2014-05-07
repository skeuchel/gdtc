Require Import String.
Require Import Names.
Require Import Arith.
Require Import Functors.

Open Scope string_scope.

Section Type_Test_Section. 
  (* Type Testing, of course. *)
  Definition D := AType.

  Definition tex1' : DType D := tnat' _. (* Nat *)
  Definition tex1 := proj1_sig tex1'.
  
  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat.").
  Eval compute in (eq_DType D tex1 tex1').

End Type_Test_Section.

Section Test_Section.

  Definition E := Arith.

  Definition ex_1 : Names.Exp E :=
    (add' _ (lit' _ 1) (lit' _ 2)).
  Definition ex_2  : Names.Exp E := 
    (add' _ (lit' _ 5) (lit' _ 0)).
  Definition ex_3  : Names.Exp E := 
      (add' _ ex_1 ex_2).

  Definition test_typeof e := 
    match (typeof D E e) with 
      | Some t1 => DTypePrint _ (proj1_sig t1)
      | None => "Type Error!"
    end.

  Eval compute in ("The type of '1 + 2' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_1)).
  Eval compute in ("The type of '145 + 2346' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_2)).
  Eval compute in ("The type of '(1 + 2) + (5 + 0)' should be tnat.").
  Eval compute in (test_typeof (proj1_sig ex_3)).
    
  Eval compute in (ExpPrint E (proj1_sig ex_1)).
  Eval compute in (ExpPrint E (proj1_sig ex_2)).
  Eval compute in (ExpPrint E (proj1_sig ex_3)).

  Definition V := StuckValue :+: BotValue :+: NatValue.

  Eval compute in ("Evaluating '1 + 2'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_1) nil))).
  Eval compute in ("Evaluating '5 + 0'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_2) nil))).
  Eval compute in ("Evaluating '(1 + 2) + (5 + 0)'").
  Eval compute in (ValuePrint V (proj1_sig (eval V E (proj1_sig ex_3) nil))).

  Definition WFV := (WFValue_VI D V).

  Lemma soundness : forall (e : Exp E),
    forall T, typeof D E (proj1_sig e) = Some T -> 
      WFValueC D V WFV (eval V E (proj1_sig e) nil) T.
  Proof.
    intro; eapply eval_Soundness; eauto with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for Arith Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
