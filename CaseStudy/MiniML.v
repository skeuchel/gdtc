Require Import Coq.Strings.String.
Require Import GDTC.
Require Import CaseStudy.Names.
Require Import CaseStudy.PNames.
Require Import CaseStudy.Arith.
Require Import CaseStudy.Bool.
Require Import CaseStudy.Lambda.
Require Import CaseStudy.Arith_Lambda.
Require Import CaseStudy.Bool_Lambda.
Require Import CaseStudy.Mu.
Require Import CaseStudy.NatCase.

Section MiniML.

  Open Scope string_scope.

  Definition D := AType :+: LType :+: BType.

  Global Instance Container_D : Container D :=
    PolynomialContainer D.

  Definition E (A : Set) := Arith :+: (Lambda D A) :+: Bool :+: (Fix_ D A) :+: (NatCase A).

  Global Instance Container_E : forall (A : Set), Container (E A).
    eauto with typeclass_instances.
  Defined.

  Definition letrec (A : Set) (t : DType D) (def : A -> Exp E A) (body : A -> Exp E A) :
    (Exp E A) := app D E (lam _ _ t body) (mu _ _ t def).

  Instance D_typeof T : FAlgebra TypeofName T (typeofR D) (E (typeofR D)).
    eauto with typeclass_instances.
  Defined.

  Definition V := StuckValue :+: BotValue :+: NatValue :+: (ClosValue E) :+: (BoolValue).

  Global Instance Container_V : Container V.
    eauto with typeclass_instances.
  Defined.

  Instance V_eval : FAlgebra EvalName (Exp E nat) (evalR V) (E nat).
    eauto 150 with typeclass_instances.
  Defined.

  Definition SV := (SubValue_refl V) ::+:: (SubValue_Bot V) ::+:: (SubValue_Clos E V).

  Global Instance Container_SV : IContainer SV.
    eauto with typeclass_instances.
  Defined.

  Global Instance EV_Alg :
    FPAlgebra (eval_continuous_Exp_P V (E nat) SV) (inject (E nat) (E nat)).
  Proof.
    repeat apply FPAlgebra_Plus_cont_inject; eauto 200 with typeclass_instances.
    - generalize (@Lambda_eval_continuous_Exp D _ _ _ E _ _ _ _).
      eauto 200 with typeclass_instances.
    - generalize (@Fix_eval_continuous_Exp D _ _ _ E _ _ _ _).
      eauto 200 with typeclass_instances.
    - generalize (@NatCase_eval_continuous_Exp E _ _ _ _).
      eauto 200 with typeclass_instances.
  Qed.

  Lemma eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _),
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n ->
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous; eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Continuity of Evaluation Proven for MiniML!").

  Definition Eqv (A B : Set) :=
    (NP_Functor_eqv E Arith A B) ::+:: (NP_Functor_eqv E Bool A B) ::+::
    (Lambda_eqv D E A B) ::+:: (Fix_eqv D E A B) ::+:: (NatCase_eqv E A B).
  Global Instance Container_Eqv : forall (A B : Set), IContainer (Eqv A B).
    eauto with typeclass_instances.
  Defined.

  Definition WFV := (WFValue_Clos D E V Eqv (typeof _ _)) ::+::
    (WFValue_Bot D V) ::+:: (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Global Instance Container_WFV : IContainer WFV.
    eauto with typeclass_instances.
  Defined.

  Instance Eval_Soundness_alg (eval_rec : Exp E nat -> evalR V) :
    iPAlgebra soundness_XName
              (soundness_X'_P D V E Eqv WFV
                              (typeof D (E (typeofR D))) eval_rec
                              (f_algebra TypeofName) (f_algebra EvalName))
              (Eqv (typeofR D) nat).
  Proof with eauto 200 with typeclass_instances.
    repeat apply iPAlgebra_Plus...
    - apply Lift_soundness_X_alg...
      apply eqv_eval_Soundness...
    - apply Lift_soundness_X_alg...
      apply eqv_eval_Soundness...
    - eapply Lambda_eqv_eval_soundness_alg...
    - eapply Fix_Soundness...
    - apply Lift_soundness_X_alg...
      eapply NatCase_eval_Soundness...
  Qed.

  Theorem soundness : forall n gamma gamma' gamma'' e' e'',
    E_eqvC _ Eqv gamma gamma' e' e'' ->
    forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
      exists T, lookup gamma b = Some T)
    (WF_gamma2 : List.length gamma = List.length gamma')
    (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
    (WF_gamma'' : WF_Environment _ _ WFV gamma'' gamma) T,
    typeof D (E _) e' = Some T -> WFValueC _ _ WFV (beval _ _ n e'' gamma'') T.
  Proof.
    eapply soundness_X; eauto 800 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for MiniML Proven!").

End MiniML.
