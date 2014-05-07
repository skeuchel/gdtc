Require Import String.
Require Import Names.
Require Import PNames.
Require Import Bool.
Require Import Lambda.
Require Import Bool_Lambda.
Require Import Functors.
(* Require Import MonadLib. *)

Open Scope string_scope.

Section Type_Test_Section. 
  (* Type Testing, of course. *)
  Definition D := BType :+: LType.

End Type_Test_Section.

Section Test_Section.

  Definition E (A : Set) := Bool :+: (Lambda D A).

  Global Instance Fun_E : forall (A : Set), 
    Functor (E A).
  Proof. 
    eauto with typeclass_instances.
  Defined.

  Instance D_typeof T : FAlgebra TypeofName T (typeofR D) (E (typeofR D)).
    eauto 150 with typeclass_instances.
  Defined.
  
  Definition V := StuckValue :+: BotValue :+: (ClosValue E) :+: BoolValue.

  Instance V_eval : FAlgebra EvalName (Exp E nat) (evalR V) (E nat).
    eauto 150 with typeclass_instances.
  Defined.

  Definition SV := (SubValue_refl V) ::+:: (SubValue_Bot V) ::+:: (SubValue_Clos E V).

   Definition EV_Alg : PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (E _) SV))) (E nat).
    eauto 150 with typeclass_instances.
   Defined.

  Definition eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _), 
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n -> 
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous with (eval_continuous_Exp_E := EV_Alg);
      eauto 150 with typeclass_instances.
  Qed.

  Eval compute in ("Continuity of Evaluation Proven!").

  Definition Eqv (A B : Set) := (NP_Functor_eqv E Bool A B) ::+:: (Lambda_eqv D E A B).
  Definition WFV := (WFValue_Clos D E V Eqv ((fun e => typeof _ _ (proj1_sig e)))) ::+:: 
    (WFValue_Bot D V) ::+:: (WFValue_VB D V).

  Instance eq_DType_eq_alg : (PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D).
    eauto 250 with typeclass_instances.
  Defined.

  Global Instance Bool_Soundness_alg P_bind P pb typeof_rec eval_rec : 
    PAlgebra eval_Soundness_alg_Name 
    (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV P_bind P
      (E (typeofR D)) (Functor_Plus Bool (Lambda D (typeofR D))) pb typeof_rec eval_rec 
      f_algebra f_algebra))) Bool.
  Proof.
    eauto 100 with typeclass_instances.
  Defined.


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
      eauto 350 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for Lambda :+: Boolean Proven!").

End Test_Section.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
