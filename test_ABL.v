Require Import String.
Require Import Names.
Require Import PNames.
Require Import Arith.
Require Import Bool.
Require Import Lambda.
Require Import Arith_Lambda.
Require Import Bool_Lambda.
Require Import Functors.
(* Require Import MonadLib. *)

Open Scope string_scope.

Section Type_Test_Section. 
  (* Type Testing, of course. *)
  Definition D := AType :+: LType :+: BType.

  Definition tex2' : DType D := tnat' _.
  Definition tex2 := proj1_sig tex2'.
  Definition tex3' : DType D := tarrow' _ tex2' tex2'. (* Nat -> Nat *)
  Definition tex3 := proj1_sig tex3'.
  Definition tex4' : DType D := tarrow' _ (tbool' _) tex2'. (* Bool -> Nat *)
  Definition tex4 := proj1_sig tex4'.
  
  Global Instance AType_eqTArrow T : FAlgebra eq_TArrowName T (eq_TArrowR D) AType :=
    {| f_algebra := @Default_eq_TArrow _ _ _ _ _ T |}.
    
  Eval compute in ("Evaluating 'tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex2 tex3').
  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex2 tex2').
  Eval compute in ("Evaluating 'tnat -> tnat == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex3 tex2').
  Eval compute in ("Evaluating 'tnat -> tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex3 (tarrow' _ tex2' tex2')).
  Eval compute in ("Evaluating 'tbool -> tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex4 (tarrow' _ tex2' tex2')).

  Eval compute in ("Evaluating 'tbool == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D (tbool _) (tnat' _)).

  Global Instance eq_TArrow_eq_D : 
    PAlgebra eq_TArrow_eqName (sig (UP'_P (eq_TArrow_eq_P D))) D.
  Proof.
    eauto 150 with typeclass_instances.
  Defined.

  Global Instance eq_DType_eq_D : 
    PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D.
    eauto 150 with typeclass_instances.
  Defined.

End Type_Test_Section.

Section Test_Section.

  Definition E (A : Set) := Arith :+: (Lambda D A) :+: Bool.

  Global Instance Fun_E : forall (A : Set), 
    Functor (E A).
  Proof. 
    eauto with typeclass_instances.
  Defined.

  Definition ex_3 A : Names.Exp (E A) := (lit' _ 1). (* ex_3 := 1 *)

  Definition ex_1 (A : Set) t1 t2 : Names.Exp (E A) := (* ex_1 := (\x : t1. x) (\y : t2 . y) *)
    app' D E (lam' D E t1 (fun e : A => var' D E e)) (lam' D E t2 (fun e : A => var' D E e)).
  Definition ex_4 A : Names.Exp (E A) := (* ex_4 := \x : tnat . x + x*)
    lam' D E (tnat' _) (fun x => @add' _ _ _ (var' D _ x) (var' D _ x)).
  Example ex_id A : Names.Exp (E A) :=  (* ex_id := \x. x *)
    lam' D _ (tnat' _) (fun x => (var' D _ x)).
  Example ex_5 A : Names.Exp (E A) := (* ex_5 := \x. (x (\y. y)) 1*)
    lam' D _ (tnat' _ ) (fun x => app' D _ (app' D _ (var' D _ x) (ex_id _)) (ex_3 _)).
  Example ex_6 A : Names.Exp (E A) := (* ex_6 := \x. \y. x y*)
    lam' D _ (tnat' _) (fun x => lam' D _ (tnat' _) (fun y => app' D _ (var' D _ x) (var' D _ y))).
  Example ex_7 A : Names.Exp (E A):= (* ex_7 := (\x. (x (\y. y)) 1) (\x. \y. x y)*)
    (app' D _ (ex_5 _) (ex_6 _)).

  Instance D_typeof T : FAlgebra TypeofName T (typeofR D) (E (typeofR D)).
    eauto with typeclass_instances.
  Defined.

  Definition test_typeof e := 
    match (typeof D (E _) e) with 
      | Some t1 => DTypePrint _ (proj1_sig t1)
      | None => "Type Error"
    end.
  
  Eval compute in ("The type of '(\x:tnat->tnat. x) (\y:tnat.y)' should be tnat->tnat").
  Eval compute in (test_typeof (proj1_sig (ex_1 _ tex3' tex2'))).
  Eval compute in ("The type of '1' as a 'Arith :+: Lambda' should be tnat").
  Eval compute in (test_typeof (proj1_sig (ex_3 _))).
  Eval compute in ("The type of '\x.x+x' as a 'Arith :+: Lambda' should be 'tnat -> tnat'").
  Eval compute in (test_typeof (proj1_sig (ex_4 _))).
    
  Eval compute in (ExpPrint _ (proj1_sig (ex_1 _ tex3' tex2'))).
  Eval compute in (ExpPrint _ (proj1_sig (ex_3 _))).
  Eval compute in (ExpPrint _ (proj1_sig (ex_4 _))).
  Eval compute in (ExpPrint _ (proj1_sig (ex_7 _))).

  Definition V := StuckValue :+: BotValue :+: NatValue :+: (ClosValue E) :+: (BoolValue).

  Instance V_eval : FAlgebra EvalName (Exp E nat) (evalR V) (E nat).
    eauto 150 with typeclass_instances.
  Defined.

  Eval compute in ("Evaluating '(\x:tnat->tnat. x) (\y:tnat.y)'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 3 (ex_1 _ tex3' tex2') nil))).
  Eval compute in ("Evaluating '((\x:tnat->tnat. x) (\y:tnat.y)) 1'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 3 (app' D E (ex_1 _ tex3' tex2') (lit' _ 1)) nil))).
  Eval compute in ("Evaluating '\x.x+x'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 2 (ex_4 _) nil))).
  Eval compute in ("Evaluating '(\x.x+x) 1'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 4 (app' D E (ex_4 _) (lit' _ 1)) nil))).
  Eval compute in ("Evaluating '(\x.x+x) 3'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 4 (app' D E (ex_4 _) (lit' _ 3)) nil))).
  Eval compute in ("Evaluating '(\x. (x (\y. y)) 1) (\x. \y. x y)'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 5 (ex_7 _) nil))).
  Eval compute in ("Evaluating '\x. x'").
  Eval compute in (ValuePrint V (proj1_sig (beval V _ 5 (ex_id _) nil))).

  Definition Eqv (A B : Set) := 
    (NP_Functor_eqv E Arith A B) ::+:: (NP_Functor_eqv E Bool A B) ::+::
    (Lambda_eqv D E A B).

  Definition WFV := (WFValue_Clos D E V Eqv ((fun e => typeof _ _ (proj1_sig e)))) ::+:: (WFValue_Bot D V) ::+:: 
    (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Definition SV := (SubValue_refl V) ::+:: (SubValue_Bot V) ::+:: (SubValue_Clos E V).
  
  Definition EV_Alg : PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (E nat) SV))) (E nat).
    eauto 200 with typeclass_instances.
  Defined.

  Lemma eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _), 
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n -> 
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous with (eval_continuous_Exp_E := EV_Alg);
      eauto with typeclass_instances.
  Qed.

  Global Instance Bool_sound P_bind P pb typeof_rec eval_rec :
    PAlgebra eval_Soundness_alg_Name
    (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV P_bind P
      (E (typeofR D)) (Fun_E (typeofR D)) pb typeof_rec
      eval_rec f_algebra f_algebra))) Bool.
  eauto 250 with typeclass_instances.
  Defined.

  Eval compute in ("Continuity of Evaluation Proven!").

  Hint Extern 0 (id _) => unfold id; eauto with typeclass_instaces : typeclass_instances.

  Theorem soundness : forall n gamma gamma' gamma'' e' e'',
    E_eqvC _ Eqv gamma gamma' e' e'' -> 
    forall (WF_gamma : forall n b, lookup gamma' n = Some b -> 
      exists T, lookup gamma b = Some T)
    (WF_gamma2 : List.length gamma = List.length gamma')
    (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n) 
    (WF_gamma'' : WF_Environment _ _ WFV gamma'' gamma) T, 
    typeof D (E _) (proj1_sig e') = Some T -> WFValueC _ _ WFV (beval _ _ n e'' gamma'') T.
  Proof.
    apply soundness_X with (eval_continuous_Exp_E := EV_Alg);
      eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for Arith :+: Lambda :+: Boolean Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
