Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import GDTC.
Require Import CaseStudy.Names.

Section Bool.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Boolean Type. *)
  Inductive BType (A : Set) : Set :=
    TBool : BType A.

  Global Instance BType_Polynomial : Polynomial BType :=
    {| PCode := U;
       pto   := fun _ x => TBool _;
       pfrom := fun _ x => eu _
    |}.
  Proof.
    intros A a; dependent destruction a; reflexivity.
    intros A a; dependent destruction a; reflexivity.
  Defined.

  Global Instance BType_Container : Container BType | 1 :=
    PolynomialContainer BType.

  Variable D : Set -> Set.
  Context `{spf_D : SPF D}.
  Definition DType := DType D.
  Context {Sub_BType_D  : BType :<: D}.

   (* Constructor + Universal Property. *)
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D}.

  Definition tbool : DType := inject BType D (TBool _).

  (* Induction Principle for Bool Types. *)
  Definition ind_alg_BType
    (P : DType -> Prop)
    (H : P tbool) : PAlgebra (inject BType D) P :=
    fun xs Axs =>
      match xs return P (inject BType D xs) with
        | TBool => H
      end.

  (* Type Equality Section. *)
  Definition isTBool : DType -> bool :=
    fun typ =>
      match project BType D typ with
        | Some TBool => true
        | None      => false
      end.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Bool (a : Set) : Set :=
  | BLit : bool -> Bool a
  | If : a -> a -> a -> Bool a.

  Inductive BoolS := SBLit : bool -> BoolS | SIf.
  Inductive BoolP : BoolS -> Set :=
  | PIfC : BoolP SIf
  | PIfT : BoolP SIf
  | PIfE : BoolP SIf.

  Definition fromBool (A : Set) (x : Bool A) : Ext BoolS BoolP A.
    destruct x.
    apply ext with (s := SBLit b).
    intro p.
    inversion p.
    apply ext with (s := SIf).
    intro p.
    inversion p.
    apply a.
    apply a0.
    apply a1.
  Defined.

  Definition toBool (A : Set) (x : Ext BoolS BoolP A) : Bool A :=
    match x with
      | ext s pf =>
        match s as s return ((BoolP s -> A) -> Bool A) with
          | SBLit n => fun pf => BLit A n
          | SIf     => fun pf => If A (pf PIfC) (pf PIfT) (pf PIfE)
        end pf
    end.

  Global Instance Bool_Container : Container Bool :=
    {| Shape    := BoolS;
       Position := BoolP;
       from     := fromBool;
       to       := toBool |}.
  Proof.
    intros A x.
    destruct x; reflexivity.
    intros A x.
    destruct x as [[] pf]; simpl;
      f_equal; extensionality p; dependent destruction p;
      reflexivity.
  Defined.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Let Exp := Fix F.
  Context {Sub_Bool_F : Bool :<: F}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_Bool_F : WF_Functor _ _ Sub_Bool_F}.
  Definition blit (b : bool) : Exp :=
    inject Bool F (BLit _ b).
  Definition cond (i t e : Exp) : Exp :=
    inject Bool F (If _ i t e).

  (* Induction Principle for Bool. *)
  Definition ind_alg_Bool
    (P : Fix F -> Prop)
    (Hblit : forall b, P (blit b))
    (Hcond : forall i t e, P i -> P t -> P e -> P (cond i t e))
      : PAlgebra (inject Bool F) P.
  Proof.
    intros xs Axs.
    destruct xs.
    apply Hblit.
    apply Hcond.
    apply (Axs PIfC).
    apply (Axs PIfT).
    apply (Axs PIfE).
  Qed.

  Definition ind2_alg_Bool
    {E E' : Set -> Set}
    `{Fun_E : SPF E}
    `{Fun_E' : SPF E'}
    {Sub_Bool_E : Bool :<: E}
    {Sub_Bool_E' : Bool :<: E'}
    (P : (Fix E) * (Fix E') -> Prop)
    (Hblit : forall b, P (inject2 Bool E E' (BLit _ b)))
    (Hcond : forall i t e (IHi : P i) (IHt : P t) (IHe : P e),
      P (inject2 Bool E E' (If _ i t e)))
      : PAlgebra (inject2 Bool E E') P.
  Proof.
    intros xs Axs.
    destruct xs.
    apply Hblit.
    apply Hcond.
    apply (Axs PIfC).
    apply (Axs PIfT).
    apply (Axs PIfE).
  Qed.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Boolmetic Expressions. *)

  Context {Eq_DType : Eq DType}.

  Definition Bool_typeof (R : Set) (rec : R -> typeofR D)
    (e : Bool R) : typeofR D :=
    match e with
      | BLit n => Some (inject BType D (TBool _))
      | If i t e => match (rec i) with
                      | Some TI =>
                        match isTBool TI with
                          | true => match (rec t), (rec e) with
                                      | Some TT, Some TE =>
                                        match eq_DType D TT TE with
                                          | true => Some TT
                                          | false => None
                                        end
                                      | _, _ => None
                                    end
                          | false => None
                        end
                      | _ => None
                    end
    end.

  Global Instance MAlgebra_typeof_Bool T:
    FAlgebra TypeofName T (typeofR D) Bool :=
    {| f_algebra := Bool_typeof T|}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Boolmetic Values. *)
  Inductive BoolValue (A : Set) : Set :=
  | VB : bool -> BoolValue A.

  Global Instance BoolValue_Container : Container BoolValue.
    apply (ConstContainer bool BoolValue
            (fun A x => match x with VB b => b end)
            VB).
    intros; reflexivity.
    destruct x; reflexivity.
  Defined.

  Variable V : Set -> Set.
  Context `{spf_V : SPF V}.
  Definition Value := Value V.
  Context {Sub_BoolValue_V : BoolValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_BoolValue_F : WF_Functor _ _ Sub_BoolValue_V}.

  Definition vb (b : bool) : Value := inject BoolValue V (VB _ b).

  (* Constructor Testing for Boolmetic Values. *)

  Definition isVB : Value -> option bool :=
    fun exp =>
      match project BoolValue V exp with
        | Some (VB b) => Some b
        | None        => None
      end.

  Lemma isVB_vb b : isVB (vb b) = Some b.
  Proof.
    unfold isVB, vb.
    rewrite project_inject.
    reflexivity.
  Qed.

  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V}.
  Context {Dis_VB_Bot : Distinct_Sub_Functor BoolValue BotValue V}.

  Lemma isVB_bot : isVB (bot _) = None.
  Proof.
    unfold isVB, bot.
    caseEq (project BoolValue V (inject BotValue V (Bot _))).
    - elimtype False.
      eapply (inject_discriminate Dis_VB_Bot b).
      unfold project, bot, inject in H.
      rewrite out_in_inverse in H.
      apply inj_prj in H.
      now unfold inject; rewrite <- H.
    - reflexivity.
  Qed.

  Lemma isBot_vb (b : bool) : isBot V (inject BoolValue V (VB _ b)) = false.
  Proof.
    unfold isBot.
    caseEq (project BotValue V (inject BoolValue V (VB _ b))).
    - elimtype False.
      eapply (inject_discriminate Dis_VB_Bot _ b0).
      unfold project, vb, inject in H.
      rewrite out_in_inverse in H.
      apply inj_prj in H.
      now unfold inject; rewrite <- H.
    - reflexivity.
  Qed.

  Context {Sub_StuckValue_V : StuckValue :<: V}.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  (* Evaluation Algebra for Boolemetic Expressions. *)

  Definition Bool_eval (R : Set) (rec : R -> evalR V)
             (e : Bool R) : evalR V :=
    match e with
      | BLit b => fun _ => vb b
      | If i t e => fun env =>
                      let i' := (rec i env) in
                      match (isVB i') with
                        | Some true => rec t env
                        | Some false => rec e env
                        | None => if isBot _ i'
                                  then bot V
                                  else stuck _ 5
                      end
    end.

  Global Instance MAlgebra_eval_Bool T :
    FAlgebra EvalName T (evalR V) Bool :=
    {| f_algebra := Bool_eval T |}.


  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.

  Global Instance MAlgebra_DTypePrint_BType T:
    FAlgebra DTypePrintName T DTypePrintR BType :=
    {| f_algebra := fun rec e => append "tbool" "" |}.

  Global Instance MAlgebra_ExpPrint_Bool T :
    FAlgebra ExpPrintName T (ExpPrintR) Bool :=
    {| f_algebra :=
         fun rec e =>
           match e with
             | BLit true => fun i => append "true" ""
             | BLit false => fun i => append "false" ""
             | If i t e => fun i' =>
               append "(if (" ((rec i i') ++ ") then (" ++ (rec t i') ++ ") else (" ++ (rec e i') ++"))")
           end
    |}.

  Global Instance MAlgebra_ValuePrint_BType T :
    FAlgebra ValuePrintName T ValuePrintR BoolValue :=
    {| f_algebra := fun rec e =>
                      match e with
                        | VB true => append "true" ""
                        | VB false => append "false" ""
                      end
    |}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName Exp (evalR V) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Bool) (F)
    (Sub_Bool_F) (MAlgebra_eval_Bool (Exp)) eval_F}.

  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context `{iSPF_F : iSPF _ SV}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

  (* Inversion principles for natural number SubValues. *)
  Definition SV_invertVB_P (i : SubValue_i V) :=
    forall b, sv_a _ i = vb b ->
      sv_b _ i = vb b.

  Inductive SV_invertVB_Name := ece_invertvb_name.
  Context {SV_invertVB_SV :
    iPAlgebra SV_invertVB_Name SV_invertVB_P SV}.

  Global Instance SV_invertVB_refl :
    iPAlgebra SV_invertVB_Name SV_invertVB_P (SubValue_refl V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVB_P.
    inversion H; subst; simpl; congruence.
  Defined.

  Lemma SV_invertVB_default : forall V'
    (Fun_V' : Functor V')
    (SV' : (SubValue_i V -> Prop) -> SubValue_i V -> Prop)
    (sub_V'_V : V' :<: V)
    (WF_V' : WF_Functor V' V sub_V'_V),
    (forall (i : SubValue_i V) (H : SV' SV_invertVB_P i),
      exists v', sv_a _ i = inject V' V v') ->
    Distinct_Sub_Functor BoolValue V' V ->
    iPAlgebra SV_invertVB_Name SV_invertVB_P SV'.
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVB_P.
    destruct (H _ H1) as [v' eq_v'].
    intros; rewrite eq_v' in H2.
    discriminate_inject H2.
  Defined.

  Global Instance SV_invertVB_Bot :
    iPAlgebra SV_invertVB_Name SV_invertVB_P (SubValue_Bot V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVB_P.
    inversion H; subst; simpl; intros.
    discriminate_inject H0.
  Defined.

  Definition SV_invertVB := ifold_ (if_algebra (iPAlgebra := SV_invertVB_SV)).

  Definition SV_invertVB'_P (i : SubValue_i V) :=
    forall n, sv_b _ i = vb n ->
      sv_a _ i = vb n \/ sv_a _ i = bot _.

  Inductive SV_invertVB'_Name := ece_invertvb'_name.
  Context {SV_invertVB'_SV :
    iPAlgebra SV_invertVB'_Name SV_invertVB'_P SV}.

  Global Instance SV_invertVB'_refl :
    iPAlgebra SV_invertVB'_Name SV_invertVB'_P (SubValue_refl V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVB'_P.
    inversion H; subst; simpl; eauto.
  Defined.

  Global Instance SV_invertVB'_Bot :
    iPAlgebra SV_invertVB'_Name SV_invertVB'_P (SubValue_Bot V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVB'_P.
    inversion H; subst; simpl; eauto.
  Defined.

  Definition SV_invertVB' := ifold_ (if_algebra (iPAlgebra := SV_invertVB'_SV)).

  (* End Inversion principles for SubValue.*)

  Context {SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.
  Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.

  (* ============================================== *)
  (* WELL-FORMED BOOLEAN VALUES                     *)
  (* ============================================== *)

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{ispf_WFV : iSPF _ WFV}.

  (** Boolean values are well-formed **)

  Inductive WFValue_VB (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop :=
  | WFV_VB : forall n v T,
    v = vb n ->
    T = tbool ->
    WFValue_VB WFV (mk_WFValue_i D V v T).

  Inductive WFV_VB_S : WFValue_i D V -> Set :=
    SWFV_VB : forall b v T,
    v = vb b ->
    T = tbool ->
    WFV_VB_S (mk_WFValue_i D V v T).

  Inductive WFV_VB_P : forall (i : WFValue_i D V), WFV_VB_S i -> Set :=.
  Definition WFV_VB_R (i : WFValue_i D V) (s : WFV_VB_S i) (p : WFV_VB_P i s) :
    WFValue_i D V := match p with end.

  Definition WFV_VB_to A i : IExt _ _ WFV_VB_R A i -> WFValue_VB A i :=
    fun x =>
      match x with
        | iext s pf =>
          match s with
            | SWFV_VB b v T e1 e2 => WFV_VB A b v T e1 e2
          end
      end.

  Definition WFV_VB_from A i : WFValue_VB A i -> IExt _ _ WFV_VB_R A i :=
    fun x => match
      x in (WFValue_VB _ i) return (IExt _ _ WFV_VB_R A i)
    with
      | WFV_VB b v T veq Teq =>
        iext _ _
             (SWFV_VB b v T veq Teq)
             (fun p : WFV_VB_P _ _ =>
                match p with end)
    end.

  Global Instance WFV_VB_Container : IContainer WFValue_VB :=
    {| IS    := WFV_VB_S;
       IP    := WFV_VB_P;
       IR    := WFV_VB_R;
       ifrom := WFV_VB_from;
       ito   := WFV_VB_to
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl.
    f_equal; extensionality p; destruct p.
  Defined.

  Definition ind_alg_WFV_VB (P : WFValue_i D V -> Prop)
    (H : forall b v T veq Teq, P (mk_WFValue_i _ _ v T))
    i (e : WFValue_VB P i) : P i :=
    match e in WFValue_VB _ i return P i with
      | WFV_VB b v T veq Teq => H b v T veq Teq
    end.

  Variable Sub_WFV_VB_WFV : Sub_iFunctor WFValue_VB WFV.
  Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

  (* Inversion principles for Well-formed Booleans. *)
  Definition WF_invertVB_P (i : WFValue_i D V) :=
    wfv_b _ _ i = tbool ->
    WFValue_VB (iFix WFV) i \/ (wfv_a D V i = bot V).

  Inductive WF_invertVB_Name := wfv_invertvb_name.
  Context {WF_invertVB_WFV :
    iPAlgebra WF_invertVB_Name WF_invertVB_P WFV}.

  Global Instance WF_invertVB_VB :
    iPAlgebra WF_invertVB_Name WF_invertVB_P WFValue_VB.
    constructor; intros.
    unfold iAlgebra; intros; unfold WF_invertVB_P.
    inversion H; subst; simpl; intros.
    left; econstructor; auto.
  Defined.

  Ltac WF_invertVB_default :=
    constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
      inversion H; simpl;
        match goal with
          eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ =>
            intro eq_H; rewrite eq_H in eq_H0;
              discriminate_inject eq_H0
        end.

  Global Instance WF_invertVB_Bot :
    iPAlgebra WF_invertVB_Name WF_invertVB_P (WFValue_Bot _ _).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold WF_invertVB_P.
    inversion H; subst; simpl; intros.
    right; reflexivity.
  Defined.

  Definition WF_invertVB := ifold_ (if_algebra (iPAlgebra := WF_invertVB_WFV)).

  Context {eq_DType_eq_DT : FPAlgebra (eq_DType_eq_P D) in_t}.

  Lemma Bool_eval_Soundness_H
    (typeof_R eval_R : Set) typeof_rec eval_rec
    {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
    {WF_eval_F' : WF_FAlgebra EvalName _ _ Bool F
      (MAlgebra_eval_Bool _) (eval_F')} :
    forall b : bool,
      forall gamma'' : Env (Names.Value V),
        forall T : Names.DType D,
          Bool_typeof typeof_R typeof_rec (BLit _ b) = Some T ->
          WFValueC D V WFV (Bool_eval eval_R eval_rec (BLit _ b) gamma'') T.
  Proof.
    intros b gamma'' T H4; intros.
    apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    simpl.
    unfold vb, inject; simpl; eauto.
    injection H4; intros; subst.
    reflexivity.
  Defined.

  Lemma Bool_eval_Soundness_H0
    (typeof_R eval_R : Set) typeof_rec eval_rec
    {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
     {WF_eval_F' : WF_FAlgebra EvalName _ _ Bool F
       (MAlgebra_eval_Bool _) (eval_F')} :
     forall (i t el : typeof_R) (i' t' el' : eval_R),
       forall gamma'' : Env (Names.Value V),
         (forall T : Names.DType D,
           typeof_rec i = Some T ->
           WFValueC D V WFV (eval_rec i' gamma'') T) ->
         (forall T : Names.DType D,
           typeof_rec t = Some T ->
           WFValueC D V WFV (eval_rec t' gamma'') T) ->
         (forall T : Names.DType D,
           typeof_rec el = Some T ->
           WFValueC D V WFV (eval_rec el' gamma'') T) ->
         forall T : Names.DType D,
           Bool_typeof typeof_R typeof_rec (If _ i t el) = Some T ->
           WFValueC D V WFV (Bool_eval eval_R eval_rec (If _ i' t' el') gamma'') T.
  Proof.
    simpl; intros i t el i' t' el' gamma'' IH_i IH_t IH_el T H4.
    caseEq (typeof_rec i); intros; rename H into typeof_i;
      unfold typeof, typeofR in typeof_i, H4; rewrite typeof_i in H4;
        try discriminate.
    caseEq (isTBool d); intros; rename H into d_eq; rewrite
      d_eq in H4; try discriminate.
    caseEq (typeof_rec t); rewrite H in H4; rename H into typeof_t.
    caseEq (typeof_rec el); rewrite H in H4; rename H into typeof_el.
    caseEq (eq_DType _ d0 d1); rewrite H in H4; rename H into eq_d0_d1.
    injection H4; intros; subst; clear H4.
    unfold isTBool in d_eq.
    caseEq (project BType D d); intros; rewrite H in d_eq;
      try discriminate; clear d_eq; rename H into d_eq; destruct b.
    apply inject_project in d_eq; eauto with typeclass_instances.
    unfold WFValueC in *|-*.
    generalize (IH_i _ typeof_i) as WF_i;
      generalize (IH_t _ typeof_t) as WF_t;
        generalize (IH_el _ typeof_el) as WF_el; intros.
    destruct (WF_invertVB _ WF_i d_eq) as [eval_i' | eval_i'];
      inversion eval_i'; subst.
    rewrite H1, isVB_vb.
    destruct n.
    apply WF_t.
    apply eq_DType_eq in eq_d0_d1; auto; subst.
    apply WF_el.
    rewrite H0; unfold bot at 1, isVB, project, inject; simpl;
      rewrite out_in_inverse; repeat rewrite wf_functor; simpl.
    caseEq (prj (Sub_Functor := Sub_BoolValue_V) (A:= Fix _) (inj (Bot _))).
    discriminate_inject H.
    rewrite isBot_bot.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; reflexivity.
    discriminate.
    discriminate.
    discriminate.
  Defined.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) F}.
  Context {WF_typeof_F : forall T, WF_FAlgebra _ _ _ _ _
    (MAlgebra_typeof_Bool T) (Typeof_F _) }.
  Context {WF_Value_continous_alg :
    iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

  Global Instance Bool_eval_Soundness_alg
    (P_bind : Set)
    (P : P_bind -> Env Value -> Prop)
    (E' : Set -> Set)
    `{spf_E' : SPF E'}
    {Sub_Bool_E' : Bool :<: E'}
    {WF_Fun_E' : WF_Functor _ _ Sub_Bool_E'}
    {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D) E'}
    {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
      Sub_Bool_E' (MAlgebra_typeof_Bool T) (Typeof_E' T)}
    (pb : P_bind)
    (eval_rec : Exp -> evalR V)
    (typeof_rec : Fix E' -> typeofR D)
    :
    FPAlgebra (eval_alg_Soundness_P D V F WFV _ P
      _ pb typeof_rec eval_rec (f_algebra TypeofName (FAlgebra := Typeof_E' _))
      (f_algebra EvalName (FAlgebra := eval_F))) (inject2 Bool E' F).
  Proof.
    constructor.
    apply ind2_alg_Bool;
    unfold eval_alg_Soundness_P, inject2, inject; simpl; intros;
    rewrite out_in_inverse; rewrite out_in_inverse in H;
    rewrite (@wf_mixin _ _ _ _ _ _ _ WF_eval_F); simpl;
    rewrite (@wf_mixin _ _ _ _ _ _ _ (WF_typeof_E' _)) in H; simpl in H.
    (* BLit Case *)
    apply Bool_eval_Soundness_H with
      (typeof_R := Fix E') (eval_R := Exp)
      (typeof_rec := typeof_rec) (eval_rec := eval_rec)
      (eval_F' := eval_F) (gamma'' := gamma''); auto.
    (* If Case *)
    apply Bool_eval_Soundness_H0 with
      (typeof_R := Fix E') (typeof_rec := typeof_rec)
      (eval_F' := eval_F) (i := fst i) (t := fst t) (el := fst e); auto.
    apply (IHa _ _ WF_gamma'' i); simpl; auto;
      intros; apply (IHi _ WF_gamma'' IHa); auto.
    apply (IHa _ _ WF_gamma'' t); simpl; auto;
      intros; apply (IHt _ WF_gamma'' IHa); auto.
    apply (IHa _ _ WF_gamma'' e); simpl; auto;
      intros; apply (IHe _ WF_gamma'' IHa); auto.
  Defined.

  (* BLit case. *)

  Lemma eval_continuous_Exp_H :
    forall b,
      eval_continuous_Exp_P V F SV (blit b).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    unfold beval, blit; simpl; unfold inject.
    rewrite out_in_inverse.
    repeat rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    apply (inject_i (subGF := Sub_SV_refl_SV)).
    constructor.
    reflexivity.
  Qed.

  (* If case. *)

  Lemma eval_continuous_Exp_H0 : forall
    (i t e : Fix F)
    (IHi : eval_continuous_Exp_P V F SV i)
    (IHt : eval_continuous_Exp_P V F SV t)
    (IHe : eval_continuous_Exp_P V F SV e),
    eval_continuous_Exp_P V F SV
      (cond i t e).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    generalize (H i _ _ _ H0 H1); simpl; intros SubV_i.
    generalize (H t _ _ _ H0 H1); simpl; intros SubV_t.
    generalize (H e _ _ _ H0 H1); simpl; intros SubV_e.
    unfold cond, inject; simpl_beval.
    unfold isVB at 2.
    caseEq (project BoolValue V (beval V F n i gamma')).
    destruct b.
    apply inject_project in H2; fold (vb b) in H2; rename H2 into Eval_i'.
    destruct (SV_invertVB' _ SubV_i _ Eval_i') as [Eval_i | Eval_i];
      simpl in Eval_i; rewrite Eval_i.
    rewrite isVB_vb; destruct b; assumption.
    rewrite isVB_bot, isBot_bot.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; reflexivity.
    unfold isVB.
    caseEq (project BoolValue V (beval V F m i gamma)).
    destruct b.
    apply inject_project in H3; rename H3 into Eval_i.
    generalize (SV_invertVB _ SubV_i _ Eval_i); simpl; intros Eval_i'.
    rewrite Eval_i' in H2.
    unfold vb in H2; rewrite project_inject in H2; discriminate.
    unfold isBot at 2.
    caseEq (project BotValue V (beval V F n i gamma')).
    destruct b.
    apply inject_project in H4; rename H4 into Eval_i'.
    generalize (SV_invertBot _ SV _ SubV_i Eval_i'); simpl; intro Eval_i.
    rewrite Eval_i, isBot_bot.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
    unfold isBot.
    caseEq (project BotValue V (beval V F m i gamma)).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; reflexivity.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
  Qed.

  Global Instance Bool_eval_continuous_Exp  :
    FPAlgebra (eval_continuous_Exp_P V F SV) (inject Bool F).
  Proof.
    constructor.
    apply ind_alg_Bool.
    apply eval_continuous_Exp_H.
    apply eval_continuous_Exp_H0.
  Defined.

End Bool.

Hint Extern 1 (iPAlgebra SV_invertVB_Name (SV_invertVB_P _) _) =>
    constructor; unfold iAlgebra; unfold SV_invertVB_P; intros i H n H0;
      inversion H; subst; discriminate_inject H0.

Hint Extern 1 (iPAlgebra SV_invertVB'_Name (SV_invertVB'_P _) _) =>
    constructor; unfold iAlgebra; unfold SV_invertVB'_P; intros i H n H0;
      inversion H; subst; discriminate_inject H0.

Ltac WF_invertVB_default :=
  constructor; unfold iAlgebra; intros i H; unfold WF_invertVB_P;
    inversion H; simpl;
      match goal with
        eq_H0 : ?T = _ |- ?T = _ -> _ =>
          intro eq_H; rewrite eq_H in eq_H0;
            discriminate_inject eq_H0
      end.

Hint Extern 5 (iPAlgebra WF_invertVB_Name (WF_invertVB_P _ _ _) _) =>
  constructor; intros i H; unfold WF_invertVB_P;
    inversion H; subst; intro eq_H;
      discriminate_inject eq_H
   : typeclass_instances.

(*
Hint Extern 0 =>
  intros; match goal with
            |- (PAlgebra eval_Soundness_alg_Name
              (sig (UP'_P2 (eval_alg_Soundness_P _ _ _ _ _ _ _ _ _ _ _ _ _ _))) Bool) =>
            eapply Bool_eval_Soundness_alg; eauto with typeclass_instances
          end : typeclass_instances.
*)
