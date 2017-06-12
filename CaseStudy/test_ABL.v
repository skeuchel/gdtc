Require Import String.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.
Require Import CaseStudy.Names.
Require Import CaseStudy.PNames.
Require Import CaseStudy.Arith.
Require Import CaseStudy.Bool.
Require Import CaseStudy.Lambda.
Require Import CaseStudy.Arith_Lambda.
Require Import CaseStudy.Bool_Lambda.

Open Scope string_scope.

Section Type_Test_Section.
  (* Type Testing, of course. *)
  Definition D := AType :+: LType :+: BType.

  Global Instance Container_D : Container D :=
    PolynomialContainer D.

  Global Instance SPF_D : SPF D.
    eauto with typeclass_instances.
  Defined.

  Definition tex2 : DType D := tnat _.
  Definition tex3 : DType D := tarrow _ tex2 tex2. (* Nat -> Nat *)
  Definition tex4 : DType D := tarrow _ (tbool _) tex2. (* Bool -> Nat *)

  Eval compute in ("Evaluating 'tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex2 tex3).
  Eval compute in ("Evaluating 'tnat == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex2 tex2).
  Eval compute in ("Evaluating 'tnat -> tnat == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex3 tex2).
  Eval compute in ("Evaluating 'tnat -> tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex3 (tarrow _ tex2 tex2)).
  Eval compute in ("Evaluating 'tbool -> tnat == tnat -> tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D tex4 (tarrow _ tex2 tex2)).

  Eval compute in ("Evaluating 'tbool == tnat' as an 'TNat :+: TArrow :+: TBool'.").
  Eval compute in (eq_DType D (tbool _) (tnat _)).

End Type_Test_Section.

Section Test_Section.

  Definition E (A : Set) := Arith :+: (Lambda D A) :+: Bool.

  Global Instance Container_E : forall (A : Set), Container (E A).
    eauto with typeclass_instances.
  Defined.

  Definition ex_3 A : Names.Exp (E A) := (lit _ 1). (* ex_3 := 1 *)

  (* Definition ex_1 (A : Set) t1 t2 : Names.Exp (E A) := (* ex_1 := (\x : t1. x) (\y : t2 . y) *) *)
  (*   app D E (lam D E t1 (fun e : A => var D E e)) (lam D E t2 (fun e : A => var D E e)). *)
  (* Definition ex_4 A : Names.Exp (E A) := (* ex_4 := \x : tnat . x + x*) *)
  (*   lam D E (tnat _) (fun x => add (E A) (var D _ x) (var D _ x)). *)
  (* Example ex_id A : Names.Exp (E A) :=  (* ex_id := \x. x *) *)
  (*   lam D _ (tnat _) (fun x => (var D _ x)). *)
  (* Example ex_5 A : Names.Exp (E A) := (* ex_5 := \x. (x (\y. y)) 1*) *)
  (*   lam D _ (tnat _ ) (fun x => app D _ (app D _ (var D _ x) (ex_id _)) (ex_3 _)). *)
  (* Example ex_6 A : Names.Exp (E A) := (* ex_6 := \x. \y. x y*) *)
  (*   lam D _ (tnat _) (fun x => lam D _ (tnat _) (fun y => app D _ (var D _ x) (var D _ y))). *)
  (* Example ex_7 A : Names.Exp (E A):= (* ex_7 := (\x. (x (\y. y)) 1) (\x. \y. x y)*) *)
  (*   (app D _ (ex_5 _) (ex_6 _)). *)

  Instance D_typeof T : FAlgebra TypeofName T (typeofR D) (E (typeofR D)).
    eauto with typeclass_instances.
  Defined.

  Definition test_typeof e :=
    match (typeof D (E _) e) with
      | Some t1 => DTypePrint _ t1
      | None => "Type Error"
    end.

  (* Eval compute in ("The type of '(\x:tnat->tnat. x) (\y:tnat.y)' should be tnat->tnat"). *)
  (* Eval compute in (test_typeof (ex_1 _ tex3 tex2)). *)
  (* Eval compute in ("The type of '1' as a 'Arith :+: Lambda' should be tnat"). *)
  (* Eval compute in (test_typeof (ex_3 _)). *)
  (* Eval compute in ("The type of '\x.x+x' as a 'Arith :+: Lambda' should be 'tnat -> tnat"). *)
  (* Eval compute in (test_typeof (ex_4 _)). *)

  (* Eval compute in (ExpPrint _ (ex_1 _ tex3 tex2)). *)
  (* Eval compute in (ExpPrint _ (ex_3 _)). *)
  (* Eval compute in (ExpPrint _ (ex_4 _)). *)
  (* Eval compute in (ExpPrint _ (ex_7 _)). *)

  Definition V := StuckValue :+: BotValue :+: NatValue :+: (ClosValue E) :+: (BoolValue).

  Global Instance Container_V : Container V.
    eauto with typeclass_instances.
  Defined.

  Instance V_eval : FAlgebra EvalName (Exp E nat) (evalR V) (E nat).
    eauto 150 with typeclass_instances.
  Defined.

  (* Eval compute in ("Evaluating '(\x:tnat->tnat. x) (\y:tnat.y)'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 3 (ex_1 _ tex3' tex2') nil))). *)
  (* Eval compute in ("Evaluating '((\x:tnat->tnat. x) (\y:tnat.y)) 1'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 3 (app D E (ex_1 _ tex3' tex2') (lit' _ 1)) nil))). *)
  (* Eval compute in ("Evaluating '\x.x+x'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 2 (ex_4 _) nil))). *)
  (* Eval compute in ("Evaluating '(\x.x+x) 1'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 4 (app D E (ex_4 _) (lit' _ 1)) nil))). *)
  (* Eval compute in ("Evaluating '(\x.x+x) 3'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 4 (app D E (ex_4 _) (lit' _ 3)) nil))). *)
  (* Eval compute in ("Evaluating '(\x. (x (\y. y)) 1) (\x. \y. x y)'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 5 (ex_7 _) nil))). *)
  (* Eval compute in ("Evaluating '\x. x'"). *)
  (* Eval compute in (ValuePrint V (proj1_sig (beval V _ 5 (ex_id _) nil))). *)

  Definition Eqv (A B : Set) :=
    (NP_Functor_eqv E Arith A B) ::+:: (NP_Functor_eqv E Bool A B) ::+::
    (Lambda_eqv D E A B).

  Global Instance Container_Eqv : forall (A B : Set), IContainer (Eqv A B).
    eauto with typeclass_instances.
  Defined.

  Definition WFV := (WFValue_Clos D E V Eqv (typeof _ _)) ::+:: (WFValue_Bot D V) ::+::
    (WFValue_VI D V) ::+:: (WFValue_VB D V).

  Global Instance Container_WFV : IContainer WFV.
    eauto with typeclass_instances.
  Defined.

  Definition SV := (SubValue_refl V) ::+:: (SubValue_Bot V) ::+:: (SubValue_Clos E V).

  Global Instance Container_SV : IContainer SV.
    eauto with typeclass_instances.
  Defined.

  Global Instance SV_invertVI_SV :
    iPAlgebra SV_invertVI_Name (SV_invertVI_P V) SV.
    repeat apply iPAlgebra_Plus; eauto 150 with typeclass_instances.
    constructor.
    unfold iAlgebra.
    unfold SV_invertVI_P.
    intros i H n H0.
    inversion H; subst.
    elimtype False; apply (inject_discriminate _ _ _ H0).
  Defined.

  Global Instance SV_invertVI'_SV :
    iPAlgebra SV_invertVI'_Name (SV_invertVI'_P V) SV.
    repeat apply iPAlgebra_Plus; eauto 150 with typeclass_instances.
    constructor.
    unfold iAlgebra.
    unfold SV_invertVI'_P.
    intros i H n H0.
    inversion H; subst.
    elimtype False; apply (inject_discriminate _ _ _ H0).
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

  Global Instance EV_Alg :
    FPAlgebra (eval_continuous_Exp_P V (E nat) SV) (inject (E nat) (E nat)).
  Proof.
    repeat apply FPAlgebra_Plus_cont_inject; eauto 200 with typeclass_instances.
    - generalize (@Lambda_eval_continuous_Exp D _ _ _ E _ _ _ _).
      eauto 200 with typeclass_instances.
  Qed.

  Lemma eval_continuous : forall m,
    forall (e : Exp E nat) (gamma gamma' : Env _),
      forall n (Sub_G_G' : Sub_Environment V SV gamma gamma'),
        m <= n ->
        SubValueC _ SV (beval _ _ m e gamma) (beval _ _ n e gamma').
    eapply beval_continuous; eauto 250 with typeclass_instances.
  Qed.

  Eval compute in ("Continuity of Evaluation Proven!").

  Hint Extern 0 (id _) => unfold id; eauto with typeclass_instaces : typeclass_instances.

 (*
  Global Instance Bool_sound P_bind P pb typeof_rec eval_rec :
    PAlgebra eval_Soundness_alg_Name
    (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV P_bind P
      (E (typeofR D)) (Fun_E (typeofR D)) pb typeof_rec
      eval_rec f_algebra f_algebra))) Bool.
  eauto 250 with typeclass_instances.
  Defined.
*)

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
    eauto 500 with typeclass_instances.
    intros.
    repeat apply iPAlgebra_Plus.
    apply Lift_soundness_X_alg.
    eauto with typeclass_instances.
    apply eqv_eval_Soundness;
    eauto 250 with typeclass_instances.
    apply Lift_soundness_X_alg.
    eauto with typeclass_instances.
    apply eqv_eval_Soundness;
    eauto 250 with typeclass_instances.
    apply (@Lambda_eqv_eval_soundness_alg D _ _ _ _ _ E _ _ _ _ V _ _ _ _ _ _ _ V_eval WF_FAlgebra_eval_Lambda _ _ Eqv _ _ _ _ WFV _ _ (typeof D (E (typeofR D)))); eauto with typeclass_instances.
    eauto 250 with typeclass_instances.
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

  Eval compute in ("Type Soundness for Arith :+: Lambda :+: Boolean Proven!").

End Test_Section.
