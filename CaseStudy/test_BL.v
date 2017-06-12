Require Import String.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.
Require Import CaseStudy.Names.
Require Import CaseStudy.PNames.
Require Import CaseStudy.Bool.
Require Import CaseStudy.Lambda.
Require Import CaseStudy.Bool_Lambda.
(* Require Import MonadLib. *)

Open Scope string_scope.

Section Type_Test_Section.
  (* Type Testing, of course. *)
  Definition D := BType :+: LType.

  Global Instance Container_D : Container D :=
    PolynomialContainer D.

End Type_Test_Section.

Section Test_Section.

  Definition E (A : Set) := Bool :+: (Lambda D A).

  Global Instance Container_E : forall (A : Set), Container (E A).
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

  Global Instance Container_SV : IContainer SV.
    eauto with typeclass_instances.
  Defined.

  Global Instance SV_invertVB_SV :
    iPAlgebra SV_invertVB_Name (SV_invertVB_P V) SV.
    repeat apply iPAlgebra_Plus; eauto 150 with typeclass_instances.
    constructor.
    unfold iAlgebra.
    unfold SV_invertVB_P.
    intros i H n H0.
    inversion H; subst.
    elimtype False; apply (inject_discriminate _ _ _ H0).
  Defined.

  Global Instance SV_invertVB'_SV :
    iPAlgebra SV_invertVB'_Name (SV_invertVB'_P V) SV.
    repeat apply iPAlgebra_Plus; eauto 150 with typeclass_instances.
    constructor.
    unfold iAlgebra.
    unfold SV_invertVB'_P.
    intros i H n H0.
    inversion H; subst.
    elimtype False; apply (inject_discriminate _ _ _ H0).
  Defined.

  Global Instance SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV.
    repeat apply iPAlgebra_Plus; eauto 150 with typeclass_instances.
  Defined.

  Global Instance EV_Alg :
    FPAlgebra (eval_continuous_Exp_P V (E nat) SV) (inject (E nat) (E nat)).
  Proof.
    apply FPAlgebra_Plus_cont_inject; eauto 200 with typeclass_instances.
    - generalize (@Lambda_eval_continuous_Exp D _ _ _ E _ _ _ _).
      eauto 200 with typeclass_instances.
  Qed.

  Definition eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _),
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n ->
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous; eauto with typeclass_instances.
  Qed.

  Eval compute in ("Continuity of Evaluation Proven!").

  Definition Eqv (A B : Set) := (NP_Functor_eqv E Bool A B) ::+:: (Lambda_eqv D E A B).
  Global Instance Container_Eqv : forall (A B : Set), IContainer (Eqv A B).
    eauto with typeclass_instances.
  Defined.

  Definition WFV := (WFValue_Clos D E V Eqv (fun e => typeof _ _ e)) ::+::
    (WFValue_Bot D V) ::+:: (WFValue_VB D V).

  Global Instance Container_WFV : IContainer WFV.
    eauto with typeclass_instances.
  Defined.

  Instance Eval_Soundness_alg :
    forall
      eval_rec : Names.Exp (E nat) -> evalR V,
      iPAlgebra soundness_XName
                (soundness_X'_P D V E Eqv WFV
                                (typeof D (E (typeofR D))) eval_rec
                                f_algebra f_algebra)
                (Eqv (typeofR D) nat).
  Proof.
    assert (WF_FAlgebra_eval_Lambda :
              WF_FAlgebra EvalName (Names.Exp (E nat)) (evalR V)
                (Lambda D nat) (E nat) (MAlgebra_eval_Lambda D E V) V_eval).
    eauto with typeclass_instances.
    intros.
    repeat apply iPAlgebra_Plus.
    apply Lift_soundness_X_alg.
    eauto with typeclass_instances.
    apply eqv_eval_Soundness;
    eauto 250 with typeclass_instances.
    apply (@Lambda_eqv_eval_soundness_alg D _ _ _ _ _ E _ _ _ _ V _ _ _ _ _ _ _ V_eval WF_FAlgebra_eval_Lambda _ _ Eqv _ _ _ _ WFV _ _ (typeof D (E (typeofR D)))); eauto with typeclass_instances.
    eauto 250 with typeclass_instances.
  Qed.

  (*
  Global Instance Bool_Soundness_alg P_bind P pb typeof_rec eval_rec :
    PAlgebra eval_Soundness_alg_Name
    (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV P_bind P
      (E (typeofR D)) (Functor_Plus Bool (Lambda D (typeofR D))) pb typeof_rec eval_rec
      f_algebra f_algebra))) Bool.
  Proof.
    eauto 100 with typeclass_instances.
  Defined.
  *)

  Theorem soundness : forall n gamma gamma' gamma'' e' e'',
    E_eqvC _ Eqv gamma gamma' e' e'' ->
    forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
      exists T, lookup gamma b = Some T)
    (WF_gamma2 : List.length gamma = List.length gamma')
    (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
    (WF_gamma'' : WF_Environment _ _ WFV gamma'' gamma) T,
    typeof D (E _) e' = Some T -> WFValueC _ _ WFV (beval _ _ n e'' gamma'') T.
  Proof.
    eapply soundness_X; eauto 350 with typeclass_instances.
  Qed.

  Eval compute in ("Type Soundness for Lambda :+: Boolean Proven!").

End Test_Section.
