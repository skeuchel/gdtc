Require Import String.
Require Import Names.
Require Import PNames.
Require Import Arith.
Require Import Bool.
Require Import Lambda.
Require Import Arith_Lambda.
Require Import Bool_Lambda.
Require Import Functors.
Require Import Mu. 
Require Import NatCase.

Section MiniML.

Open Scope string_scope.

Definition D := AType :+: LType :+: BType.

Definition E (A : Set) := Arith :+: (Lambda D A) :+: Bool :+: (Fix_ D A) :+: (NatCase A).

Definition letrec (A : Set) (t : DType D) (def : A -> Exp E A) (body : A -> Exp E A) : 
  (Exp E A) :=  app' D E (lam' _ _ t body) (mu' _ _ t def).
  
Instance D_typeof T : FAlgebra TypeofName T (typeofR D) (E (typeofR D)).
  eauto with typeclass_instances.
Defined.

Global Instance Fun_E : forall (A : Set), 
  Functor (E A).
Proof. 
  eauto with typeclass_instances.
Defined.

  Definition V := StuckValue :+: BotValue :+: NatValue :+: (ClosValue E) :+: (BoolValue).

  Instance V_eval : FAlgebra EvalName (Exp E nat) (evalR V) (E nat).
    unfold V, E, D.
    auto 20 with typeclass_instances.
  Defined.

  Global Instance eq_DType_eq_D : 
    PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D.
  Proof.
    unfold D.
    eauto 20 with typeclass_instances.
  Defined.

  Definition Eqv (A B : Set) := 
    (NP_Functor_eqv E Arith A B) ::+:: (NP_Functor_eqv E Bool A B) ::+::
    (Lambda_eqv D E A B) ::+:: (Fix_eqv D E A B) ::+:: (NatCase_eqv E A B).

  Definition WFV := (WFValue_Clos D E V Eqv (fun e => typeof _ _ (proj1_sig e))) ::+::
    (WFValue_Bot D V) ::+:: (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Definition SV := (SubValue_refl V) ::+:: (SubValue_Bot V) ::+:: (SubValue_Clos E V).
  
  Definition EV_Alg : PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (E nat) SV))) (E nat).
    eauto 400 with typeclass_instances.
  Defined.

  Definition eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _), 
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n -> 
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous with (eval_continuous_Exp_E := EV_Alg);
      eauto 800 with typeclass_instances.
  Qed.

  Eval compute in ("Continuity of Evaluation Proven for MiniML!").

  Global Instance Bool_sound P_bind P pb typeof_rec eval_rec :
    PAlgebra eval_Soundness_alg_Name
    (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV P_bind P
      (E (typeofR D)) (Fun_E (typeofR D)) pb typeof_rec
      eval_rec f_algebra f_algebra))) Bool.
  eauto 250 with typeclass_instances.
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
      eauto 800 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for MiniML Proven!").

End MiniML.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
