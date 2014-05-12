Require Import String.
Require Import Polynomial.
Require Import Containers.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
(* Require Import MonadLib. *)

Section NatCase.

  Open Scope string_scope.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {PFun_D : PFunctor D}.
  Context {SPF_D : SPF D}.

  Definition DType := DType D.
  Context {Sub_AType_D  : AType :<: D}.

  Inductive NatCase (A E : Set) : Set :=
  | NVar : A -> NatCase A E
  | Case : E -> E -> (A -> E) -> NatCase A E.

  Global Instance NatCase_Iso (A : Set) :
    Iso (NatCase A) (K A :+: Id :*: Id :*: Fn A) :=
    {| fromIso := fun E e => match e with
                               | NVar a       => inl a
                               | Case e1 e2 f => inr (e1,(e2,f))
                             end;
       toIso   := fun E e => match e with
                               | inl a           => NVar _ _ a
                               | inr (e1,(e2,f)) => Case _ _ e1 e2 f
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [n|[x [y f]]]; reflexivity.
  Defined.

  Global Instance NatCase_Container (A : Set) : Container (NatCase A) :=
    ContainerIso (NatCase_Iso A).

  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Context {PFun_F : forall A, PFunctor (F A)}.
  Context {SPF_F : forall A, SPF (F A)}.
  Definition Exp A := Exp (F A).
  Context {Sub_NatCase_F : forall A, NatCase A :<: F A}.
  Context {WF_Sub_NatCase_F : forall A, WF_Functor _ _ (Sub_NatCase_F A)}.

  Definition nvar {A : Set} n : Exp A := inject (NVar _ _ n).
  Definition case {A : Set} n z s : Exp A := inject (Case _ _ n z s).

  Definition ind_alg_NatCase {A : Set}
    (P : Fix' (F A) -> Prop)
    (Hnvar : forall x, P (nvar x))
    (Hcase : forall e1 e2 f, P e1 -> P e2 -> (forall a, P (f a)) -> P (case e1 e2 f))
  : PAlgebra (inject' (NatCase A)) P :=
    fun xs =>
      match xs return All P xs -> P (inject' (NatCase A) xs) with
        | NVar a       => fun _ => Hnvar a
        | Case e1 e2 f => fun Axs : forall p : _ + _, _ =>
                            Hcase e1 e2 f
                                  (Axs (inl tt))
                                  (Axs (inr (inl tt)))
                                  (fun a => Axs (inr (inr a)))
      end.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  Context {Eq_DType : Eq DType}.

  Definition NatCase_typeof (R : Set) (rec : R -> typeofR D)
    (e : NatCase (typeofR D) R) : typeofR D :=
     match e with
       | NVar n => n
       | Case n z s =>
         match (rec n) with
           | Some Tn =>
             match isTNat _ Tn with
               | true => match rec z, rec (s (Some (tnat _))) with
                           | Some TZ, Some TS =>
                             match eq_DType D TZ TS with
                               | true => Some TZ
                               | false => None
                             end
                           | _, _ => None
                         end
               | false => None
             end
           | _ => None
         end
     end.

  Global Instance MAlgebra_typeof_NatCase T:
    FAlgebra TypeofName T (typeofR D) (NatCase (typeofR D)) :=
    {| f_algebra := NatCase_typeof T|}.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {PFun_V : PFunctor V}.
  Context {SPF_V : SPF V}.
  Definition Value := Value V.
  Context {Sub_NatValue_V : NatValue :<: V}.
  Context {WF_SubNatValue_V : WF_Functor NatValue V Sub_NatValue_V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V}.

  Definition NatCase_eval R : Mixin R (NatCase nat) (evalR V) :=
    fun rec e =>
      match e with
        | NVar n =>
          fun env => match (lookup env n) with
                       | Some v => v
                       | _ => stuck _ 146
                     end
        | Case n z s =>
          fun env =>
            let reced := rec n env in
            match isVI V reced with
              | Some 0 => rec z env
              | Some (S n') => rec (s (Datatypes.length env)) (insert _ (vi _ n') env)
              | _ => if isBot _ reced then bot _ else stuck _ 145
            end
      end.

  Global Instance MAlgebra_eval_NatCase T :
    FAlgebra EvalName T (evalR V) (NatCase _) :=
    {| f_algebra := NatCase_eval T|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import Ascii.
  Require Import String.

  Definition NatCase_ExpPrint (R : Set) (rec : R -> ExpPrintR)
    (e : NatCase nat R) : ExpPrintR :=
    match e with
      | NVar n => fun n => "n" ++ (String (ascii_of_nat n) EmptyString)
      | Case n z s => fun i => append "(case (" ((rec n i) ++ ") of
  | 0 => " ++ (rec z i) ++ "
  | S n" ++ (String (ascii_of_nat i) EmptyString) ++ " => " ++
  rec (s i) (S i)) ++ ")"
    end.

  Global Instance MAlgebra_Print_NatCase T :
     FAlgebra ExpPrintName T ExpPrintR (NatCase nat) :=
     {| f_algebra := NatCase_ExpPrint T|}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (NatCase _)
    (F _) (Sub_NatCase_F _) (MAlgebra_eval_NatCase _) (eval_F)}.

  (* Continuity of Evaluation. *)

  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context {iFun_SV : iFunctor SV}.
  Context {iSPF_SV : iSPF SV}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.
  Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.
  Context {SV_invertVI_SV :
    iPAlgebra SV_invertVI_Name (SV_invertVI_P V) SV}.
  Context {SV_invertVI'_SV :
    iPAlgebra SV_invertVI'_Name (SV_invertVI'_P V) SV}.
  Context {Dis_VI_Bot : Distinct_Sub_Functor NatValue BotValue V}.
  Context {SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.

  Global Instance NatCase_eval_continuous_Exp  :
    FPAlgebra (eval_continuous_Exp_P V (F nat) SV) (inject' (NatCase nat)).
  Proof.
    constructor; unfold PAlgebra; intros.
    apply ind_alg_NatCase; auto; intros.
    (* NVar case. *)
    unfold eval_continuous_Exp_P; intros.
    unfold nvar, inject; simpl_beval.
    caseEq (@lookup Value gamma x); unfold Value, Arith.Value in *|-*;
      rewrite H3.
    destruct (P2_Env_lookup _ _ _ _ _ H1 _ _ H3) as [v' [lookup_v' Sub_v_v']].
    unfold Value; rewrite lookup_v'; eauto.
    unfold Value; rewrite (P2_Env_Nlookup _ _ _ _ _ H1 _ H3).
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    (* Case case. *)
    rename H0 into IHn, H1 into IHz, H2 into IHf.
    unfold eval_continuous_Exp_P; intros.
    generalize (H0 e1 _ _ _ H1 H2); simpl; intros SubV_e1.
    generalize (H0 e2 _ _ _ H1 H2); simpl; intros SubV_e2.
    unfold case, inject; simpl_beval.
    unfold isVI at 2.
    rewrite <- (P2_Env_length _ _ _ _ _ H1).
    caseEq (project (G := NatValue) (beval V (F _) n e1 gamma')).
    destruct n0.
    apply inject_project in H3; rename H3 into Eval_e1'.
    destruct (SV_invertVI' _ _ SubV_e1 _ Eval_e1') as [Eval_e1 | Eval_e1];
      simpl in Eval_e1; rewrite Eval_e1.
    rewrite isVI_vi.
    destruct n0; auto.
    apply H0; auto.
    apply P2_Env_insert; auto.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
    rewrite isVI_bot; auto.
    rewrite isBot_bot.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; reflexivity; auto.
    unfold isVI at 1.
    caseEq (project (G := NatValue) (beval V (F nat) m e1 gamma)).
    destruct n0.
    apply inject_project in H4; rename H4 into Eval_e1.
    generalize (SV_invertVI _ _ SubV_e1 _ Eval_e1); simpl; intros Eval_e1'.
    rewrite Eval_e1' in H3.
    unfold vi in H3; rewrite project_inject in H3; discriminate.
    unfold isBot at 2.
    caseEq (project (G := BotValue) (beval V (F nat) n e1 gamma')).
    destruct b.
    apply inject_project in H5; rename H5 into Eval_e1'.
    generalize (SV_invertBot _ SV _ SubV_e1 Eval_e1'); simpl; intro Eval_e1.
    rewrite Eval_e1, isBot_bot.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
    unfold isBot.
    caseEq (project (G := BotValue) (beval V (F nat) m e1 gamma)).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; reflexivity; auto.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
  Defined.

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context {ifun_WFV : iFunctor WFV}.
  Context {ispf_WFV : iSPF WFV}.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Definition E_eqv A B := iFix' (EQV_E A B).
  Definition E_eqvC {A B : Set} gamma gamma' e e' :=
    E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').

  (* Projection doesn't affect Equivalence Relation.*)

  Inductive NatCase_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
  | NVar_eqv : forall (gamma : Env _) gamma' n a b,
    lookup gamma n = Some a -> lookup gamma' n = Some b ->
    NatCase_eqv A B E (mk_eqv_i _ _ _ gamma gamma' (nvar a) (nvar b))
  | Case_eqv : forall (gamma : Env _) gamma' n n' z z' s s',
    E (mk_eqv_i _ _ _ gamma gamma' n n') ->
    E (mk_eqv_i _ _ _ gamma gamma' z z') ->
    (forall (n : A) (n' : B),
      E (mk_eqv_i _ _ _ (insert _ n gamma) (insert _ n' gamma') (s n) (s' n'))) ->
    NatCase_eqv _ _ E (mk_eqv_i _ _ _ gamma gamma' (case n z s) (case n' z' s')).

  Inductive NatCase_eqv_S (A B : Set) : eqv_i F A B -> Set :=
  | SNVar_eqv : forall (gamma : Env _) gamma' n a b,
    lookup gamma n = Some a -> lookup gamma' n = Some b ->
    NatCase_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (nvar a) (nvar b))
  | SCase_eqv : forall (gamma : Env _) gamma' n n' z z' s s',
    NatCase_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (case n z s) (case n' z' s')).

  Definition NatCase_eqv_P (A B : Set) (i : eqv_i F A B) (s : NatCase_eqv_S A B i) : Set :=
    match s with
      | SNVar_eqv _ _ _ _ _ _ _ => Empty_set
      | SCase_eqv _ _ _ _ _ _ _ _ => (unit + unit + A * B)%type
    end.

  Definition NatCase_eqv_R (A B : Set) (i : eqv_i F A B)
    (s : NatCase_eqv_S A B i)
    (p : NatCase_eqv_P A B i s) : eqv_i F A B.
  Proof.
    destruct s; simpl in p.
    destruct p.
    destruct p as [[p|p]|[a b]].
    apply (mk_eqv_i _ _ _ gamma gamma' n n').
    apply (mk_eqv_i _ _ _ gamma gamma' z z').
    apply (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (s a) (s' b)).
  Defined.

  Definition NatCase_eqv_to (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    IExt _ _ (NatCase_eqv_R A B) C i -> NatCase_eqv A B C i.
  Proof.
    intros x; destruct x; destruct s; simpl in pf.
    constructor 1 with (n := n); auto.
    constructor 2.
    apply (pf (inl (inl tt))).
    apply (pf (inl (inr tt))).
    intros a b.
    apply (pf (inr (a,b))).
  Defined.

  Definition NatCase_eqv_from (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    NatCase_eqv A B C i -> IExt _ _ (NatCase_eqv_R A B) C i.
  Proof.
    intros x; destruct x.
    constructor 1 with (s := SNVar_eqv _ _ gamma gamma' n a b H H0); simpl.
    intro p; destruct p.
    constructor 1 with (s := SCase_eqv _ _ gamma gamma' n n' z z' s s'); simpl.
    intro p; destruct p as [[p|p]|[a b]]; auto.
  Defined.

  Global Instance NatCase_eqv_Container (A B : Set) : IContainer (NatCase_eqv A B) :=
    {| IS    := NatCase_eqv_S A B;
       IP    := NatCase_eqv_P A B;
       IR    := NatCase_eqv_R A B;
       ifrom := NatCase_eqv_from A B;
       ito   := NatCase_eqv_to A B
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl; f_equal.
    extensionality p; destruct p.
    extensionality p; destruct p as [[[]|[]]|[a b]]; reflexivity.
  Defined.

  Definition ind_alg_NatCase_eqv
    (A B : Set)
    (P : eqv_i F A B -> Prop)
    (H : forall gamma gamma' n a b lookup_a lookup_b,
      P (mk_eqv_i _ _ _ gamma gamma' (nvar a) (nvar b)))
    (H0 : forall gamma gamma' n n' z z' s s'
      (IHn : P (mk_eqv_i _ _ _ gamma gamma' n n'))
      (IHz : P (mk_eqv_i _ _ _ gamma gamma' z z'))
      (IHs : forall n n',
        P (mk_eqv_i _ _ _ (insert _ n gamma) (insert _ n' gamma') (s n) (s' n'))),
    P (mk_eqv_i _ _ _ gamma gamma' (case n z s) (case n' z' s')))
    i (e : NatCase_eqv A B P i) : P i :=
    match e in NatCase_eqv _ _ _ i return P i with
      | NVar_eqv gamma gamma' n a b lookup_a lookup_b =>
        H gamma gamma' n a b lookup_a lookup_b
      | Case_eqv gamma gamma' n n' z z' s s'
        eqv_n_n' eqv_z_z' eqv_s_s' =>
        H0 gamma gamma' n n' z z' s s' eqv_n_n'
        eqv_z_z' eqv_s_s'
    end.

  Variable Sub_NatCase_eqv_EQV_E : forall A B,
    Sub_iFunctor (NatCase_eqv A B) (EQV_E A B).

  Lemma isTNat_tnat :
    forall (T : DType),
      isTNat _ T = true -> T = tnat _.
  Proof.
    unfold isTNat; intros T.
    caseEq (project (G := AType) T).
    apply inject_project in H.
    destruct a; exact H.
    discriminate.
  Defined.

  Context {WF_invertVI_WFV : iPAlgebra WF_invertVI_Name (WF_invertVI_P D V WFV) WFV}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) (F (typeofR D))}.
  Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
    (Sub_NatCase_F _) (MAlgebra_typeof_NatCase _) (Typeof_F _)}.
  Context {eval_F' : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {WF_eval_F' : @WF_FAlgebra EvalName _ _ (NatCase _)
    (F _) (Sub_NatCase_F _) (MAlgebra_eval_NatCase _) (eval_F')}.
  Variable Sub_WFV_VI_WFV : Sub_iFunctor (WFValue_VI D V) WFV.
  Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

  Global Instance NatCase_eval_Soundness
    (eval_rec : Exp _ -> evalR V)
    (typeof_rec : Exp _ -> typeofR D) :
    iPAlgebra eqv_eval_SoundnessName
    (eqv_eval_alg_Soundness'_P D V F EQV_E WFV typeof_rec eval_rec
      (f_algebra (FAlgebra := Typeof_F _ ))
      (f_algebra (FAlgebra := eval_F'))) (NatCase_eqv _ _).
  Proof.
    econstructor; unfold iAlgebra; intros.
    eapply ind_alg_NatCase_eqv; unfold eqv_eval_alg_Soundness'_P,
       eval_alg_Soundness_P; simpl; intros; try assumption.
    (* NVar Case *)
    split; intros.
    apply inject_i; econstructor; eauto.
    unfold nvar, inject; simpl.
    rewrite out_in_inverse.
    rewrite (wf_mixin (WF_Mixin := WF_eval_F')); simpl.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]];
      simpl in *|-*.
    rewrite (WF_gamma' _ _ lookup_b) in *|-*.
    destruct (P2_Env_lookup' _ _ _ _ _ WF_gamma'' _ _ lookup_a) as [v [lookup_v WF_v]];
      unfold Value; rewrite lookup_v.
    destruct a; eauto.
    rename H0 into typeof_d.
    unfold nvar, inject in typeof_d;
      rewrite out_in_inverse in typeof_d;
        rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)) in typeof_d;
          simpl in typeof_d; injection typeof_d; intros; subst; auto.
    destruct WF_v.
    (* Ncase Case *)
    destruct IHn as [n_eqv IHn]; destruct IHz as [z_eqv IHz];
      generalize (fun n n' => (proj1 (IHs n n'))) as s_eqv;
        generalize (fun n n' => (proj2 (IHs n n'))) as IHs'; intros;
          clear IHs; rename IHs' into IHs.
    split; intros.
    apply inject_i; constructor; auto.
    generalize H0; clear H0.
    unfold case, inject; repeat rewrite out_in_inverse.
    rewrite (wf_mixin (WF_Mixin := WF_eval_F'));
      rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)); simpl.
    caseEq (typeof_rec n);
      rename H0 into typeof_n; try discriminate.
    rename H1 into H0.
    assert (WF_a : WFValueC D V WFV (eval_rec n' gamma'') d)
      by (apply (IHa _ _ WF_gamma'' (n, n')); intros; auto; apply IHn; auto).
    caseEq (isTNat D d); rename H1 into d_eq;
      rewrite d_eq in H0; try discriminate; apply isTNat_tnat in d_eq; subst.
    eapply WF_invertVI in WF_a; eauto with typeclass_instances.
    destruct WF_a as [beval_a' | beval_a']; auto; simpl;
      inversion beval_a'; subst.
    rename H2 into eval_n'.
    caseEq (typeof_rec z);
      rename H1 into typeof_z; rewrite typeof_z in H0; try discriminate.
    caseEq (typeof_rec (s (Some (tnat D))));
      rename H1 into typeof_s; rewrite typeof_s in H0; try discriminate.
    caseEq (eq_DType _ d d0); rewrite H1 in H0; try discriminate;
      rename H1 into eq_d0; injection H0; intros; subst.
    apply eq_DType_eq in eq_d0; subst.
    rewrite isVI_vi; destruct n0.
      (* zero case *)
      apply (IHa _ _ WF_gamma'' (z, z')); intros; auto.
      (* successor case *)
      assert (WF_eqv_environment_P D V WFV
           (insert _ (Some (tnat _)) gamma,
            insert _ (Datatypes.length gamma') gamma')
           (insert _ (vi V n0) gamma'')).
      destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
      unfold WF_eqv_environment_P; simpl; repeat split.
      simpl in WF_gamma2; rewrite <- WF_gamma2.
      revert WF_gamma; clear; simpl; induction gamma';
        destruct m; simpl; intros; try discriminate.
      injection H; intros; subst.
      clear; induction gamma; simpl; eauto; eexists.
      injection H; intros; subst.
      generalize b (WF_gamma 0 _ (eq_refl _)); clear; induction gamma; simpl; intros b H;
        destruct H as [T lookup_T]; try discriminate.
      destruct b; eauto.
      eapply IHgamma'.
      intros n0 b0 H0; eapply (WF_gamma (S n0) _ H0).
      eassumption.
      assert (exists m', Datatypes.length gamma' = m') as m'_eq
        by (eexists _; reflexivity); destruct m'_eq as [m' m'_eq].
      rewrite m'_eq; generalize m' gamma' WF_gamma2; clear; induction gamma;
        destruct gamma'; intros; simpl; try discriminate;
          try injection H7; intros; eauto.
      simpl in *|-*.
      intro; caseEq (beq_nat m (Datatypes.length gamma')).
      assert (exists m', m' = Datatypes.length gamma') as ex_m' by
        (eexists _; reflexivity); destruct ex_m' as [m' m'_eq];
          rewrite <- m'_eq in H2 at 1.
      rewrite (beq_nat_true _ _ H1), <- m'_eq.
      rewrite (beq_nat_true _ _ H1) in H2.
      generalize m' b H2; clear.
      induction gamma'; simpl; intros;
           try discriminate; auto.
      congruence.
      auto.
      apply WF_gamma'.
      assert (exists m', m' = Datatypes.length gamma') as ex_m' by
        (eexists _; reflexivity); destruct ex_m' as [m' m'_eq];
          rewrite <- m'_eq in H2 at 1.
      generalize m' m (beq_nat_false _ _ H1) H2; clear;
        induction gamma'; simpl; destruct m; intros;
          try discriminate; eauto.
      contradict H; reflexivity.
      apply P2_Env_insert;
        [assumption | apply (inject_i (subGF := Sub_WFV_VI_WFV));
          econstructor; unfold vi; auto].
      assert (WFValueC D V WFV (eval_rec (s' (Datatypes.length gamma''))
        (insert (Arith.Value V) (vi V n0) gamma'')) d0) as WF_s'.
      apply (IHa _ _ H1 (s (Some (tnat D)), s' (Datatypes.length gamma''))).
      intros; simpl.
      destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
      apply IHs with (n := Some (tnat D)); auto.
      simpl in *|-*; rewrite (P2_Env_length _ _ _ _ _ WF_gamma'').
      rewrite <- WF_gamma2 in H1; apply H1.
      exact typeof_s.
      auto.
    rewrite H2.
    rewrite isVI_bot; auto.
    rewrite isBot_bot.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
  Defined.

End NatCase.
