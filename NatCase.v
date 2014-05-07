Require Import String.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
(* Require Import MonadLib. *)

Section NatCase.

  Open Scope string_scope.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_AType_D  : AType :<: D}.
  
  Inductive NatCase (A E : Set) : Set :=
  | NVar : A -> NatCase A E
  | Case : E -> E -> (A -> E) -> NatCase A E.
  
  Definition NatCase_fmap (A B C : Set) (f : B -> C) (Aa : NatCase A B) : NatCase A C :=
    match Aa with 
      | NVar n => NVar _ _ n
      | Case n z s => Case _ _ (f n) (f z) (fun n' => f (s n'))
    end.
  
  Global Instance NatCase_Functor A : Functor (NatCase A) :=
    {| fmap := NatCase_fmap A |}.
  Proof. 
    destruct a; reflexivity.
  (* fmap id *)
    destruct a; unfold id; simpl; auto.
    rewrite <- eta_expansion_dep; reflexivity.
  Defined.  
  
  Variable F : Set -> Set -> Set.
  Context {Fun_F : forall A, Functor (F A)}.
  Definition Exp A := Exp (F A).
  Context {Sub_NatCase_F : forall A, NatCase A :<: F A}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_NatCase_F : forall A, WF_Functor _ _ (Sub_NatCase_F A) _ _}.

  Definition nvar' {A : Set} n : Exp A := inject' (NVar _ _ n).
  Definition nvar {A : Set} n : Fix (F A) := proj1_sig (nvar' n).
  Definition nvar_UP' {A : Set} n : 
    Universal_Property'_fold (nvar (A := A) n) :=
    proj2_sig (nvar' n).

  Definition case' {A : Set} n z s : Exp A := inject' (Case _ _ n z s).
  Definition Ncase {A : Set} n z s {n_UP'} {z_UP'} {s_UP'} : Fix (F A) :=
    proj1_sig (case' (exist _ n n_UP') (exist _ z z_UP')
      (fun n' => exist _ (s n') (s_UP' n'))).
  Definition Ncase_UP' {A : Set} n z s {n_UP'} {z_UP'} {s_UP'} : 
    Universal_Property'_fold (Ncase (A := A) n z s) :=
    proj2_sig (case' (exist _ n n_UP') (exist _ z z_UP')
      (fun n' => exist _ (s n') (s_UP' n'))).

  Definition ind_alg_NatCase {A : Set}
    (P : forall e : Fix (F A), Universal_Property'_fold e -> Prop) 
    (H : forall n, UP'_P P (@nvar A n))
    (H0 : forall n z s
      (IHn : UP'_P P n) 
      (IHz : UP'_P P z)
      (IHs : forall n', UP'_P P (s n')),
      UP'_P P (@Ncase A n z s (proj1_sig IHn) (proj1_sig IHz) (fun n' => proj1_sig (IHs n'))))
      (e : NatCase A (sig (UP'_P P))) 
        : 
        sig (UP'_P P) :=
    match e with
      | NVar n => exist (UP'_P P) _ (H n)
      | Case n z s => exist (UP'_P P) _
        (H0 (proj1_sig n) (proj1_sig z) (fun n' => proj1_sig (s n'))
          (proj2_sig n) (proj2_sig z) (fun n' => proj2_sig (s n')))
    end.

(* ============================================== *)
(* TYPING                                         *)
(* ============================================== *)

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.

  Definition NatCase_typeof (R : Set) (rec : R -> typeofR D) 
    (e : NatCase (typeofR D) R) : typeofR D := 
     match e with 
       | NVar n => n
       | Case n z s => 
         match (rec n) with
           | Some Tn => 
             match isTNat _ (proj1_sig Tn) with
               | true => match rec z, rec (s (Some (tnat' _))) with 
                           | Some TZ, Some TS => 
                             match eq_DType D (proj1_sig TZ) TS with 
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
  Definition Value := Value V.
  Context {Sub_NatValue_V : NatValue :<: V}.
  Context {WF_SubNatValue_V : WF_Functor NatValue V Sub_NatValue_V _ _}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Definition stuck' : nat -> Value := stuck' _.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V _ _}.
  Definition bot' : Value := bot' _.

  Definition NatCase_eval R : Mixin R (NatCase nat) (evalR V) :=
    fun rec e => 
     match e with 
       | NVar n => fun env => match (lookup env n) with 
                                | Some v => v 
                                | _ => stuck' 146
                              end
       | Case n z s => fun env => 
         let reced := rec n env in 
           match isVI V (proj1_sig reced) with 
             | Some 0 => rec z env 
             | Some (S n') => rec (s (Datatypes.length env)) (insert _ (vi' _ n') env)
             | _ => if isBot _ (proj1_sig reced) then bot' else stuck' 145
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
    Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.
    Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.
    Context {SV_invertVI_SV :
      iPAlgebra SV_invertVI_Name (SV_invertVI_P V) SV}.        
    Context {SV_invertVI'_SV :
      iPAlgebra SV_invertVI'_Name (SV_invertVI'_P V) SV}.    
    Context {Dis_VI_Bot : Distinct_Sub_Functor _ Sub_NatValue_V Sub_BotValue_V}.
    Context {SV_invertBot_SV :
      iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.

    Context {SV_proj1_b_SV :
      iPAlgebra SV_proj1_b_Name (SV_proj1_b_P _ SV) SV}.    
    Context {SV_proj1_a_SV :
      iPAlgebra SV_proj1_a_Name (SV_proj1_a_P _ SV) SV}.    

    Global Instance NatCase_eval_continuous_Exp  : 
      PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V (F _) SV))) (NatCase nat).
    Proof.
      constructor; unfold Algebra; intros.
      eapply ind_alg_NatCase; try assumption; intros.
    (* NVar case. *)
      unfold eval_continuous_Exp_P; econstructor; simpl; intros;
        eauto with typeclass_instances.
      instantiate (1 := nvar_UP' n).
      unfold beval, mfold, nvar; simpl; repeat rewrite wf_functor; simpl.
      repeat rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      caseEq (@lookup _ gamma n); unfold Value in *|-*.
      destruct (P2_Env_lookup _ _ _ _ _ H1 _ _ H3) as [v' [lookup_v' Sub_v_v']].
      unfold Value; rewrite lookup_v'; eauto.
      unfold Value; rewrite (P2_Env_Nlookup _ _ _ _ _ H1 _ H3).
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    (* Case case. *)
      destruct IHn as [n_UP IHn].
      destruct IHz as [z_UP IHz].
      unfold eval_continuous_Exp_P; econstructor; simpl; intros;
        eauto with typeclass_instances.
      instantiate (1 := Ncase_UP' _ _ _).
      destruct (IHs (Datatypes.length gamma)) as [s'_UP IHs'].
      generalize (H0 (exist _ _ n_UP) _ _ _ H1 H2); intro SV_n_n.
      unfold beval, mfold, Ncase; simpl; repeat rewrite wf_functor; simpl.
      repeat rewrite out_in_fmap; rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      rewrite <- (P2_Env_length _ _ _ _ _ H1).
      repeat erewrite bF_UP_in_out.
      unfold Names.Exp, evalR.
      unfold isVI; caseEq (project (proj1_sig (beval V (F _) n0 (exist _ _ n_UP) gamma'))).
      unfold beval, Names.Exp, evalR in H3; rewrite H3.
      destruct n1.
      apply project_inject in H3; auto with typeclass_instances; 
        unfold inject, evalR, Names.Value in H3; simpl in H3.
      destruct (SV_invertVI' V _ SV_n_n _ H3) as [beval_m | beval_m]; 
        simpl in beval_m; unfold beval, Names.Exp, evalR in *|-*; rewrite beval_m.
      rewrite project_vi_vi; eauto; destruct n1; apply H0; auto.
      (eapply P2_Env_insert; 
        [assumption | apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto]).
      rewrite project_vi_bot; eauto.
      unfold isBot; rewrite project_bot_bot; eauto.
      apply inject_i; constructor; reflexivity.
      exact (proj2_sig _).
      unfold isBot; caseEq (project (G := BotValue)
        (proj1_sig (beval V (F _) n0 (exist _ _ n_UP) gamma'))).
      unfold beval, Names.Exp, evalR in H4; rewrite H4.
      destruct b.
      apply project_inject in H4; auto with typeclass_instances; 
        unfold inject, evalR, Names.Value in H4; simpl in H4.
      generalize (SV_invertBot V _ _ _ SV_n_n H4) as beval_m; intro;
        simpl in beval_m; unfold beval, Names.Exp, evalR in *|-*; rewrite beval_m.
      rewrite project_vi_bot, project_bot_bot; eauto.
      apply inject_i; constructor; reflexivity.
      exact (proj2_sig _).
      unfold isVI; caseEq (project (proj1_sig (beval V (F _) m (exist _ _ n_UP) gamma))).
      unfold beval, Names.Exp, evalR in H5; rewrite H5.
      destruct n1.
      apply project_inject in H5; auto with typeclass_instances; 
        unfold inject, evalR, Names.Value in H5; simpl in H5.
      generalize (SV_invertVI V _ SV_n_n _ H5) as beval_m; intro;
        simpl in beval_m; unfold Names.Exp, evalR in *|-*; rewrite beval_m in H3.
      rewrite project_vi_vi in H3; eauto; discriminate.
      exact (proj2_sig _).
      unfold beval, Names.Exp, evalR in H5; rewrite H5.
      caseEq (project (G := BotValue)
        (proj1_sig (beval V (F _) m (exist _ _ n_UP) gamma))).
      unfold beval, Names.Exp, evalR in H6; rewrite H6.
      destruct b.
      apply inject_i; constructor; reflexivity.
      unfold beval, Names.Exp, evalR in H6; rewrite H6.
      unfold beval, Names.Exp, evalR in H3; rewrite H3.
      unfold beval, Names.Exp, evalR in H4; rewrite H4.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; reflexivity.
    Defined.

    Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
    Variable funWFV : iFunctor WFV.
    Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
    Definition E_eqv A B := iFix (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' := 
      E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').
    Variable funEQV_E : forall A B, iFunctor (EQV_E A B).

    (* Projection doesn't affect Equivalence Relation.*)

    Inductive NatCase_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
    | NVar_eqv : forall (gamma : Env _) gamma' n a b e e', 
      lookup gamma n = Some a -> lookup gamma' n = Some b -> 
      proj1_sig e = nvar a -> 
      proj1_sig e' = nvar b -> 
      NatCase_eqv A B E (mk_eqv_i _ _ _ gamma gamma' e e')
    | Case_eqv : forall (gamma : Env _) gamma' n n' z z' s s' e e', 
      E (mk_eqv_i _ _ _ gamma gamma' n n') -> 
      E (mk_eqv_i _ _ _ gamma gamma' z z') -> 
      (forall (n : A) (n' : B), 
        E (mk_eqv_i _ _ _ (insert _ n gamma) (insert _ n' gamma') (s n) (s' n'))) -> 
      proj1_sig e = proj1_sig (case' n z s) ->
      proj1_sig e' = proj1_sig (case' n' z' s') ->  
      NatCase_eqv _ _ E (mk_eqv_i _ _ _ gamma gamma' e e').

    Definition ind_alg_NatCase_eqv 
      (A B : Set)
      (P : eqv_i F A B -> Prop) 
      (H : forall gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq,
        P (mk_eqv_i _ _ _ gamma gamma' e e'))
      (H0 : forall gamma gamma' n n' z z' s s' e e'       
        (IHn : P (mk_eqv_i _ _ _ gamma gamma' n n'))
        (IHz : P (mk_eqv_i _ _ _ gamma gamma' z z'))
        (IHs : forall n n', 
          P (mk_eqv_i _ _ _ (insert _ n gamma) (insert _ n' gamma') (s n) (s' n')))
        e_eq e'_eq, 
      P (mk_eqv_i _ _ _ gamma gamma' e e'))
      i (e : NatCase_eqv A B P i) : P i :=
      match e in NatCase_eqv _ _ _ i return P i with 
        | NVar_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq => 
          H gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | Case_eqv gamma gamma' n n' z z' s s' e e'
          eqv_n_n' eqv_z_z' eqv_s_s' e_eq e'_eq => 
          H0 gamma gamma' n n' z z' s s' e e' eqv_n_n'
          eqv_z_z' eqv_s_s' e_eq e'_eq
      end.

    Definition NatCase_eqv_ifmap (A B : Set)
      (A' B' : eqv_i F A B -> Prop) i (f : forall i, A' i -> B' i) 
      (eqv_a : NatCase_eqv A B A' i) : NatCase_eqv A B B' i :=
      match eqv_a in NatCase_eqv _ _ _ i return NatCase_eqv _ _ _ i with
        | NVar_eqv gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq => 
          NVar_eqv _ _ _ gamma gamma' n a b e e' lookup_a lookup_b e_eq e'_eq
        | Case_eqv gamma gamma' n n' z z' s s' e e'
          eqv_n_n' eqv_z_z' eqv_s_s' e_eq e'_eq => 
          Case_eqv _ _ _ gamma gamma' n n' z z' s s' e e' 
          (f _ eqv_n_n') (f _ eqv_z_z')
          (fun a b => f _ (eqv_s_s' a b))
          e_eq e'_eq
      end.

    Global Instance iFun_NatCase_eqv A B : iFunctor (NatCase_eqv A B).
      constructor 1 with (ifmap := NatCase_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; unfold id; eauto.
      rewrite (functional_extensionality_dep _ a1); eauto.
      intros; apply functional_extensionality_dep; eauto.
    Defined.

    Variable Sub_NatCase_eqv_EQV_E : forall A B, 
      Sub_iFunctor (NatCase_eqv A B) (EQV_E A B).

     Global Instance EQV_proj1_NatCase_eqv : 
       forall A B, iPAlgebra EQV_proj1_Name (EQV_proj1_P F EQV_E A B) (NatCase_eqv _ _).
       econstructor; intros.
       unfold iAlgebra; intros; apply ind_alg_NatCase_eqv; 
         unfold EQV_proj1_P; simpl; intros; subst.
       apply (inject_i (subGF := Sub_NatCase_eqv_EQV_E A B)); econstructor; simpl; eauto.
       apply (inject_i (subGF := Sub_NatCase_eqv_EQV_E A B)); econstructor 2; simpl; eauto.
       destruct n; destruct n'; eapply IHn; eauto.
       destruct z; destruct z'; eapply IHz; eauto.
       intros; caseEq (s n0); caseEq (s' n'0); apply IHs; eauto.
       rewrite H2; simpl; eauto.
       rewrite H3; simpl; eauto.
       apply H.
     Qed.

  Lemma isTNat_tnat : forall T : DType, 
    isTNat _ (proj1_sig T) = true -> proj1_sig T = tnat _.
    unfold isTNat; intros; caseEq (project (G := AType) (proj1_sig T));
      rewrite H0 in H; try discriminate.
    destruct a; unfold project in H0; apply inj_prj in H0.
    apply (f_equal (in_t_UP' _ _)) in H0;
      apply (f_equal (@proj1_sig _ _)) in H0; 
        rewrite in_out_UP'_inverse in H0.
    eauto.
    exact (proj2_sig _).
  Defined.
  
  Lemma isVI_vi : forall n,
    isVI _ (vi _ n) = Some n.
    intros; unfold isVI, vi, vi', project; simpl; rewrite wf_functor.
    rewrite out_in_fmap; rewrite wf_functor; simpl.
    rewrite prj_inj; reflexivity.
  Qed.

  Lemma isVI_bot : isVI _ (bot _) = None.
    intros; unfold isVI, bot, bot', project; simpl; rewrite wf_functor.
    rewrite out_in_fmap; rewrite wf_functor; simpl; unfold Bot_fmap.
    caseEq (prj (sub_F := NatValue) (inj (Bot (sig (@Universal_Property'_fold V _))))); auto.
    apply inj_prj in H.
    elimtype False.
    eapply (inject_discriminate Dis_VI_Bot n (Bot _)).
    unfold inject; erewrite H; reflexivity.
  Qed.

  Lemma isBot_bot : isBot _ (bot _) = true.
    intros; unfold isBot, bot, bot', project; simpl; rewrite wf_functor.
    rewrite out_in_fmap; rewrite wf_functor; simpl; unfold Bot_fmap.
    rewrite prj_inj; reflexivity.
  Qed.

  Context {WF_invertVI_WFV : iPAlgebra WF_invertVI_Name (WF_invertVI_P D V WFV) WFV}.    
  Context {eq_DType_eq_DT : PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) D}.
  Variable WF_Ind_DType_eq_D : WF_Ind eq_DType_eq_DT.
  Context {WFV_proj1_a_WFV :
    iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFV}.    
  Context {WFV_proj1_b_WFV :
    iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFV}.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) (F (typeofR D))}.
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
    rewrite e'_eq.
    split; intros.
    apply inject_i; econstructor; eauto.
    unfold nvar, nvar'; simpl. erewrite out_in_fmap;
    repeat rewrite wf_functor; simpl.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_F')); simpl.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]]; 
      simpl in *|-*.
    rewrite (WF_gamma' _ _ lookup_b) in *|-*.
    destruct (P2_Env_lookup' _ _ _ _ _ WF_gamma'' _ _ lookup_a) as [v [lookup_v WF_v]];
      unfold Value; rewrite lookup_v.
    destruct a; eauto.
    rename H0 into typeof_d.
    rewrite e_eq in typeof_d; unfold typeof, mfold, nvar in typeof_d;
      simpl in typeof_d; rewrite wf_functor in typeof_d; simpl in typeof_d;
        rewrite out_in_fmap in typeof_d; rewrite wf_functor in typeof_d;
          simpl in typeof_d;
            rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)) in typeof_d;
              simpl in typeof_d; injection typeof_d; intros; subst; auto.
    destruct WF_v.
    (* Ncase Case *)
    rewrite e'_eq.
    destruct IHn as [n_eqv IHn]; destruct IHz as [z_eqv IHz]; 
      generalize (fun n n' => (proj1 (IHs n n'))) as s_eqv;
        generalize (fun n n' => (proj2 (IHs n n'))) as IHs'; intros;
          clear IHs; rename IHs' into IHs.
    split; intros.
    apply inject_i; econstructor 2.
    apply n_eqv.
    apply z_eqv.
    apply s_eqv.
    auto.
    auto.
    erewrite out_in_fmap; repeat rewrite wf_functor; simpl.
    rewrite (wf_algebra (WF_FAlgebra := WF_eval_F')); simpl.
    rewrite e_eq in H0.
    erewrite out_in_fmap in H0; repeat rewrite wf_functor in H0; simpl in H0.
    rewrite (wf_algebra (WF_FAlgebra := WF_typeof_F _)) in H0; simpl.
    simpl in H0.
    caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig n))));
      rename H1 into typeof_n; rewrite typeof_n in H0; try discriminate.
    assert (WFValueC D V WFV (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig n'))) gamma'') d) 
      as WF_a by
        (apply (IHa _ _ WF_gamma'' (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig n)), n')); 
          intros; auto; apply IHn; auto;
            unfold fst in H1; rewrite in_out_UP'_inverse in H1; auto;
              exact (proj2_sig _)).
    unfold isTNat, project in H0.
    caseEq (prj (sub_F := AType) (out_t_UP' _ _ (proj1_sig d))); 
      rename H1 into d_eq; rewrite d_eq in H0; try discriminate; apply inj_prj in d_eq.
    apply (f_equal (fun e => proj1_sig (in_t_UP' _ _ e))) in d_eq.
    destruct a; rewrite in_out_UP'_inverse in d_eq.
    destruct (WF_invertVI D V WFV _ _ WF_a d_eq) as [beval_a' | beval_a']; 
      inversion beval_a'; subst.
    rewrite H3; rename H3 into eval_n'.
    caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig z)))); 
      rename H1 into typeof_z; rewrite typeof_z in H0; try discriminate.
    caseEq (typeof_rec (in_t_UP' _ _ (out_t_UP' _ _  (proj1_sig (s (Some (tnat' D)))))));
      rename H1 into typeof_s; rewrite typeof_s in H0; try discriminate.
    rewrite isVI_vi; destruct n0.
    assert (WFValueC D V WFV (eval_rec  (in_t_UP' _ _  (out_t_UP' _ _ (proj1_sig z'))) gamma'') d0) as WF_z'.
    apply (IHa _ _ WF_gamma'' (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig z)), z'));
      intros; auto; apply IHz; auto;
      unfold fst in H1; rewrite in_out_UP'_inverse in H1; auto;
        exact (proj2_sig _).
    caseEq (eq_DType _ (proj1_sig d0) d1); rewrite H1 in H0; try discriminate;
      rename H1 into eq_d0; injection H0; intros; subst.
    generalize (WFV_proj1_a D V WFV _ _ WF_z' _ (proj2_sig _) (refl_equal _));
      simpl.
    destruct (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig z'))) gamma''); simpl; auto.
    caseEq (eq_DType _ (proj1_sig d0) d1); rewrite H1 in H0; try discriminate;
      rename H1 into eq_d0; injection H0; intros; subst.
    assert (WF_eqv_environment_P D V WFV (insert _ (Some (tnat' _)) gamma, 
      insert _ (Datatypes.length gamma') gamma') 
    (insert _ (vi' V n0) gamma'')).
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
         try discriminate.
    congruence.
    eauto.
    eapply WF_gamma'.
    assert (exists m', m' = Datatypes.length gamma') as ex_m' by 
      (eexists _; reflexivity); destruct ex_m' as [m' m'_eq]; 
        rewrite <- m'_eq in H2 at 1.
    generalize m' m (beq_nat_false _ _ H1) H2; clear; 
      induction gamma'; simpl; destruct m; intros;
        try discriminate; eauto.
    elimtype False; eauto.
    eapply P2_Env_insert; 
      [assumption | apply (inject_i (subGF := Sub_WFV_VI_WFV));
        econstructor; unfold vi; auto].
    assert (WFValueC D V WFV (eval_rec (in_t_UP' _ _  
      (out_t_UP' _ _ (proj1_sig (s' (Datatypes.length gamma''))))) 
      (insert (Arith.Value V) (vi' V n0) gamma'')) d1) as WF_s'.    
    eapply (IHa _ _ H1 (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig _)), _)); eauto.
    intros.
    simpl.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
    eapply IHs; eauto.
    simpl in *|-*; rewrite (P2_Env_length _ _ _ _ _ WF_gamma'').
    rewrite <- WF_gamma2 in H1; apply H1.
    unfold fst in H2; rewrite in_out_UP'_inverse in H2.
    apply H2.
    exact (proj2_sig _).
    generalize (WFV_proj1_b D V WFV _ _ WF_s' _ (proj2_sig _) 
      (eq_DType_eq D WF_Ind_DType_eq_D _ _ eq_d0)); simpl.
    destruct T; auto.
    rewrite H2.
    rewrite isVI_bot.
    rewrite isBot_bot.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); econstructor; eauto.
    exact (proj2_sig _).
  Defined.

End NatCase.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***


*** End: ***
*) 
