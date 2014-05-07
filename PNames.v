Require Import Functors.
Require Import List.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Section PNames. 

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)
  
  (** SuperFunctor for Types. **)
  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  
  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)
  
  (** SuperFunctor for Values. **)
  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {WF_SubStuckValue_V : WF_Functor _ _ Sub_StuckValue_V _ _}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V _ _}.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)
 
  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set -> Set.
  Context {Fun_E : forall A, Functor (E A)}.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)
 
  (** TYPING **)

  Context {Typeof_E : forall T,
    FAlgebra TypeofName T (typeofR D) (E (typeofR D))}.

  Context {eval_E : forall T, FAlgebra EvalName T (evalR V) (E nat)}.
  Context {beval_E : FAlgebra EvalName (Exp (E nat)) (evalR V) (E nat)}.

  (* ============================================== *)
  (* EXPRESSION EQUIVALENCE RELATION                *)
  (* ============================================== *)

  Section eqv_Section.
    
    Record eqv_i (A B : Set) : Set := mk_eqv_i 
      {env_A : Env A;
        env_B : Env B;
        eqv_a : UP'_F (E A);
        eqv_b : UP'_F (E B)}.

    (** SuperFunctor for Equivalence Relation. **)
    Variable EQV_E : forall A B,
      (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.

    Definition E_eqv A B := iFix (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' := 
      E_eqv _ _ (mk_eqv_i A B gamma gamma' e e').

    Variable (NP : Set -> Set).
    Context {Fun_NP : Functor NP}.
    Context {sub_NP_F : forall A, NP :<: E A}.

    Inductive NP_Functor_eqv 
      (A B : Set) 
      (C : eqv_i A B -> Prop)
      : eqv_i A B -> Prop :=
    | NP_eqv_0 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, NP D),
      proj1_sig e = inject (subGF := sub_NP_F A) (np _) ->
      proj1_sig e' = inject (subGF := sub_NP_F B) (np _) ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C'), 
        fmap f (np A') = fmap g (np B')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_1 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> NP D)
      a a', 
      proj1_sig e = inject (subGF := sub_NP_F A) (np _ a) ->
      proj1_sig e' = inject (subGF := sub_NP_F B) (np _ a') ->
      C (mk_eqv_i _ _ gamma gamma' a a') -> 
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' : A') (b' : B'), f a' = g b' ->
        fmap f (np A' a') = fmap g (np B' b')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_2 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> NP D)
      a a' b b', 
      proj1_sig e = inject (subGF := sub_NP_F A) (np _ a b) ->
      proj1_sig e' = inject (subGF := sub_NP_F B) (np _ a' b') ->
      C (mk_eqv_i _ _ gamma gamma' a a') -> 
      C (mk_eqv_i _ _ gamma gamma' b b') -> 
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' : A') (b' b'' : B'), f a' = g b' -> f a'' = g b'' ->
        fmap f (np A' a' a'') = fmap g (np B' b' b'')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_3 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> D -> NP D)
      a a' b b' c c', 
      proj1_sig e = inject (subGF := sub_NP_F A) (np _ a b c) ->
      proj1_sig e' = inject (subGF := sub_NP_F B) (np _ a' b' c') ->
      C (mk_eqv_i _ _ gamma gamma' a a') -> 
      C (mk_eqv_i _ _ gamma gamma' b b') -> 
      C (mk_eqv_i _ _ gamma gamma' c c') -> 
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' a''' : A') (b' b'' b''' : B'), 
        f a' = g b' -> f a'' = g b'' -> f a''' = g b''' -> 
        fmap f (np A' a' a'' a''') = fmap g (np B' b' b'' b''')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e').

    Definition ind_alg_NP_Functor_eqv 
      (A B : Set)
      (P : eqv_i A B -> Prop) 
      (H : forall gamma gamma' e e' np e_eq e'_eq wf_np,
        P (mk_eqv_i _ _ gamma gamma' e e'))
      (H0 : forall gamma gamma' e e' np a a' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      (H1 : forall gamma gamma' e e' np a a' b b' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _  gamma gamma' b b')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      (H2 : forall gamma gamma' e e' np a a' b b' c c' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _  gamma gamma' b b'))
        (IHc : P (mk_eqv_i _ _  gamma gamma' c c')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      i (e : NP_Functor_eqv A B P i) : P i :=
      match e in NP_Functor_eqv _ _ _  i return P i with 
        | NP_eqv_0 gamma gamma' e e' np e_eq e'_eq wf_np => 
          H gamma gamma' e e' np e_eq e'_eq wf_np
        | NP_eqv_1 gamma gamma' e e' np a a' e_eq e'_eq a_eqv wf_np => 
          H0 gamma gamma' e e' np a a' e_eq e'_eq a_eqv wf_np 
        | NP_eqv_2 gamma gamma' e e' np a a' b b' e_eq e'_eq a_eqv b_eqv wf_np => 
          H1 gamma gamma' e e' np a a' b b' e_eq e'_eq a_eqv b_eqv wf_np
        | NP_eqv_3 gamma gamma' e e' np a a' b b' c c' e_eq e'_eq a_eqv b_eqv c_eqv wf_np  => 
          H2 gamma gamma' e e' np a a' b b' c c' e_eq e'_eq a_eqv b_eqv c_eqv wf_np 
      end.

    Definition NP_Functor_eqv_ifmap 
      (A B : Set)
      (A' B' : eqv_i A B -> Prop) i (f : forall i, A' i -> B' i) 
      (eqv_a : NP_Functor_eqv A B A' i) : 
      NP_Functor_eqv A B B' i :=
      match eqv_a in NP_Functor_eqv _ _ _ i return NP_Functor_eqv _ _ _ i with
        | NP_eqv_0 gamma gamma' e e' np e_eq e'_eq wf_np => 
          NP_eqv_0 _ _ _ gamma gamma' e e' np e_eq e'_eq wf_np
        | NP_eqv_1 gamma gamma' e e' np a a' e_eq e'_eq a_eqv wf_np => 
          NP_eqv_1 _ _ _ gamma gamma' e e' np a a' e_eq e'_eq (f _ a_eqv) wf_np
        | NP_eqv_2 gamma gamma' e e' np a a' b b' e_eq e'_eq a_eqv b_eqv wf_np => 
          NP_eqv_2 _ _ _ gamma gamma' e e' np a a' b b' e_eq e'_eq (f _ a_eqv) (f _ b_eqv) wf_np
        | NP_eqv_3 gamma gamma' e e' np a a' b b' c c' e_eq e'_eq a_eqv b_eqv c_eqv wf_np => 
          NP_eqv_3 _ _ _ gamma gamma' e e' np a a' b b' c c' e_eq e'_eq (f _ a_eqv) (f _ b_eqv) (f _ c_eqv) wf_np
      end.

    Global Instance iFun_Arith_eqv A B : iFunctor (NP_Functor_eqv A B).
      constructor 1 with (ifmap := NP_Functor_eqv_ifmap A B).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    (* Projection doesn't affect Equivalence Relation.*)

     Definition EQV_proj1_P A B (i : eqv_i A B) := 
      forall a' b' H H0, a' = proj1_sig (eqv_a _ _ i) -> 
        b' = proj1_sig (eqv_b _ _ i) -> 
        E_eqvC (env_A _ _ i) (env_B _ _ i) (exist _ a' H) (exist _ b' H0).

     Inductive EQV_proj1_Name := eqv_proj1_name.
     Context {EQV_proj1_EQV : forall A B, 
       iPAlgebra EQV_proj1_Name (@EQV_proj1_P A B) (EQV_E A B)}.    
     Context {Fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.

     Definition EQV_proj1 A B:= 
       ifold_ (EQV_E A B) _ (ip_algebra (iPAlgebra := EQV_proj1_EQV A B)).
     
    Variable Sub_NP_Functor_eqv_EQV_E : forall A B, 
      Sub_iFunctor (NP_Functor_eqv A B) (EQV_E A B).

     Global Instance EQV_proj1_NP_Functor_eqv : 
       forall A B, 
         iPAlgebra EQV_proj1_Name (EQV_proj1_P A B) (NP_Functor_eqv _ _).
     Proof. 
       intros; econstructor; unfold iAlgebra; intros.
       eapply ind_alg_NP_Functor_eqv; unfold EQV_proj1_P; simpl; intros.
       apply inject_i; econstructor; simpl; eauto.
       rewrite H2; rewrite e_eq; eauto.
       rewrite H3; rewrite e'_eq; eauto.
       apply inject_i; econstructor 2; simpl; eauto.
       rewrite H2; rewrite e_eq; eauto.
       rewrite H3; rewrite e'_eq; eauto.
       destruct a; destruct a'; apply IHa; auto.
       apply inject_i; econstructor 3; simpl; eauto.
       rewrite H2; rewrite e_eq; eauto.
       rewrite H3; rewrite e'_eq; eauto.
       destruct a; destruct a'; apply IHa; auto.
       destruct b; destruct b'; apply IHb; auto.
       apply inject_i; econstructor 4; simpl; eauto.
       rewrite H2; rewrite e_eq; eauto.
       rewrite H3; rewrite e'_eq; eauto.
       destruct a; destruct a'; apply IHa; auto.
       destruct b; destruct b'; apply IHb; auto.
       destruct c; destruct c'; apply IHc; auto.
       assumption.
     Defined.

   End eqv_Section.

   Variable EQV_E : forall A B, (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.
   Context {Fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
   Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
   Context {funWFV : iFunctor WFV}.     

   Definition WF_eqv_environment_P (env_A_B : Env (typeofR D) * Env nat) gamma'' :=
     (forall m b : nat,
       lookup (snd env_A_B) m = Some b ->
       exists T, lookup (fst env_A_B) b = Some T) /\
     Datatypes.length (fst env_A_B) = Datatypes.length (snd env_A_B) /\
     (forall m b : nat, lookup (snd env_A_B) m = Some b -> b = m) /\
     WF_Environment _ _ WFV gamma'' (fst env_A_B).

    Definition eqv_eval_alg_Soundness'_P 
      (typeof_rec : Exp (E (typeofR D)) -> typeofR D)
      (eval_rec : Exp (E nat) -> evalR V)
      (typeof_F : Mixin (Exp (E (typeofR D))) (E (typeofR D)) (typeofR D))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalR V))
      i := 
      E_eqv EQV_E _ _ i /\
      eval_alg_Soundness_P D V (E nat) WFV 
      _ WF_eqv_environment_P
      (E (typeofR D)) _ (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec 
      typeof_F eval_F
      (proj1_sig (eqv_a _ _ i), proj1_sig (eqv_b _ _ i))
      (conj (proj2_sig (eqv_a _ _ i)) (proj2_sig (eqv_b _ _ i))).
    
    Lemma WF_eqv_environment_P_insert : forall gamma gamma' gamma'' v T,
      WF_eqv_environment_P (gamma, gamma') gamma'' -> 
      WFValueC _ _ WFV v T -> 
      WF_eqv_environment_P (insert _ (Some T) gamma, insert _ (Datatypes.length gamma') gamma')
      (insert _ v gamma'').
    Proof.
      intros; destruct H as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
      unfold WF_eqv_environment_P; simpl in *|-*; repeat split.
      rewrite <- WF_gamma2.
      revert WF_gamma; clear; simpl; induction gamma';
        destruct m; simpl; intros; try discriminate.
      injection H; intros; subst.
      clear; induction gamma; simpl; eauto; eexists.
      injection H; intros; subst.
      generalize b (WF_gamma 0 _ (eq_refl _)); clear; induction gamma; simpl; intros b H;
        destruct H as [T' lookup_T']; try discriminate.
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
          rewrite <- m'_eq in H at 1.
      rewrite <- WF_gamma2 in H1.
      rewrite (beq_nat_true _ _ H).
      rewrite (beq_nat_true _ _ H), m'_eq in H1.
      rewrite <- WF_gamma2 in m'_eq; rewrite m'_eq.      
      generalize m' b H1; clear.
      induction gamma'; simpl; intros; try discriminate.
      injection H1; auto.
      eauto.
      eapply WF_gamma'.
      rewrite <- WF_gamma2 in H1.
      assert (exists m', m' = Datatypes.length gamma') as ex_m' by 
      (eexists _; reflexivity); destruct ex_m' as [m' m'_eq].
      generalize m' m (beq_nat_false _ _ H) H1; clear; 
        induction gamma'; simpl; destruct m; intros;
          try discriminate; eauto.
      elimtype False; eauto.
      eapply P2_Env_insert.
      eauto.
      apply H0.
    Qed.

    Section NP_beval_Soundness.

    Variable (NP : Set -> Set).
    Context {Fun_NP : Functor NP}.
    Context {sub_NP_F : forall A, NP :<: E A}.
    Context {WF_sub_NP_F_V : forall A, WF_Functor _ _ (sub_NP_F A) _ _}.

    Variable Sub_NP_Functor_eqv_EQV_E : forall A B, 
      Sub_iFunctor (NP_Functor_eqv NP A B) (EQV_E A B).

    Context {eval_Soundness_alg_NP : forall pb typeof_rec eval_rec,
      PAlgebra eval_Soundness_alg_Name (sig (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV 
        _ WF_eqv_environment_P (E (typeofR D)) _ pb typeof_rec eval_rec 
        (f_algebra (FAlgebra := Typeof_E _)) (f_algebra (FAlgebra := beval_E))))) NP}.
    (* Context {WF_Ind_eval_Soundness_alg : forall pb typeof_rec eval_rec, 
      @WF_Ind2 (E _) (E _) NP eval_Soundness_alg_Name (Fun_E _) (Fun_E _) Fun_NP
      (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV _ _
        (E (typeofR D)) _ pb typeof_rec eval_rec _ _)) _ _ (eval_Soundness_alg_NP pb _ _)}. *)

    Variable WF_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV.

    Inductive eqv_eval_SoundnessName : Set := eqv_eval_soundnessname.

    Context {Typeof_NP : forall T, FAlgebra TypeofName T (typeofR D) NP}.
    Context {beval_NP : FAlgebra EvalName (Exp (E nat)) (evalR V) NP}.
    Context {WF_eval_F : @WF_FAlgebra EvalName _ _ NP (E _)
      (sub_NP_F _) beval_NP (eval_E _)}.
    Context {WF_typeof_F : @WF_FAlgebra TypeofName _ _ NP (E _)
      (sub_NP_F _) (Typeof_NP _) (Typeof_E (Fix (E (typeofR D))))}.

    Global Instance eqv_eval_Soundness typeof_rec eval_rec :
      forall (WF_Ind_eval_Soundness_alg : forall pb, 
        @WF_Ind2 (E _) (E _) NP eval_Soundness_alg_Name (Fun_E _) (Fun_E _) Fun_NP
        (UP'_P2 (eval_alg_Soundness_P D V (E nat) WFV _ _
          (E (typeofR D)) _ pb typeof_rec eval_rec _ _)) _ _ (eval_Soundness_alg_NP pb _ _)),
      iPAlgebra eqv_eval_SoundnessName 
      (eqv_eval_alg_Soundness'_P typeof_rec eval_rec 
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E))) (NP_Functor_eqv _ _ _).
    Proof. 
      econstructor; unfold iAlgebra; intros.
      eapply ind_alg_NP_Functor_eqv; try eassumption; 
        unfold eqv_eval_alg_Soundness'_P; simpl; intros.
      split.
      apply inject_i; econstructor; eauto.
      (* generalize (proj1_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma') typeof_rec eval_rec) (np _)). *)
      generalize (proj1_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) (np _)).
      generalize (proj2_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg
        (gamma, gamma')) (np _)).
      intros e1_eq e2_eq.
      destruct (p_algebra (PAlgebra := eval_Soundness_alg_NP 
        (gamma, gamma') typeof_rec eval_rec)) as
      [[e1 e2] [[UP_e1 UP_e2] sound_e1]]; auto; simpl in *|-*.      
      destruct e as [e e_UP]; destruct e' as [e' e'_UP]; simpl.
      simpl in *|-*.
      revert sound_e1.
      unfold eval_alg_Soundness_P; simpl.
      repeat rewrite e_eq, e'_eq, e1_eq, e2_eq; simpl.
      intros sound_e1 proj1_eval gamma'' WF_gamma'' IHa T;
        generalize (sound_e1 proj1_eval gamma'' WF_gamma'' IHa T); intros.
      unfold inject; simpl.
      rewrite wf_functor.
      erewrite wf_np.    
      apply H0.
      erewrite wf_np.
      unfold inject in H1; simpl in H1; rewrite wf_functor in H1.
      apply H1.
      destruct IHa as [eqv_a IHa]; split; intros.
      apply inject_i; econstructor 2; eauto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV 
          _ WF_eqv_environment_P (E (typeofR D))
          (Fun_E (typeofR D)) (gamma, gamma') typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig a, proj1_sig a')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      unfold eval_alg_Soundness_P; intros.
      apply IHa; auto.
      generalize (proj1_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) 
      (np _ (exist _ (proj1_sig a, proj1_sig a') H0))).
      generalize (proj2_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) 
        (np _ (exist _(proj1_sig a, proj1_sig a') H0))).
      intros e1_eq e2_eq.
      destruct (p_algebra (PAlgebra := eval_Soundness_alg_NP 
        (gamma, gamma') typeof_rec eval_rec)) as
        [[e1 e2] [[UP_e1 UP_e2] sound_e1]]; auto; simpl in *|-*.      
      destruct e as [e e_UP]; destruct e' as [e' e'_UP]; simpl.
      simpl in *|-*.
      revert sound_e1.
      unfold eval_alg_Soundness_P; simpl.
      repeat rewrite e_eq, e'_eq, e1_eq, e2_eq; simpl.
      intros sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0 T; 
        generalize (sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0 T).
      intros; unfold inject; simpl.
      rewrite wf_functor.
      erewrite wf_np.    
      apply H1.
      erewrite wf_np.
      unfold inject in H2; simpl in H2; rewrite wf_functor in H2.
      apply H2.
      simpl; auto.
      simpl; auto.
      destruct IHa as [a_eqv IHa]; destruct IHb as [b_eqv IHb].
      split; intros.
      apply inject_i; econstructor 3; eauto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV 
          _ WF_eqv_environment_P (E (typeofR D)) (Fun_E (typeofR D))
          (gamma, gamma') typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig a, proj1_sig a')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      apply IHa; auto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV _ WF_eqv_environment_P
          (E (typeofR D)) (Fun_E (typeofR D)) 
          (gamma, gamma') typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig b, proj1_sig b')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      apply IHb; auto.
      generalize (proj1_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) 
      (np _ (exist _ (proj1_sig a, proj1_sig a') H0)
        (exist _ (proj1_sig b, proj1_sig b') H1))).
      generalize (proj2_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) 
      (np _ (exist _ (proj1_sig a, proj1_sig a') H0)
        (exist _ (proj1_sig b, proj1_sig b') H1))).
      simpl.
      intros e1_eq e2_eq.
      destruct (p_algebra (PAlgebra := eval_Soundness_alg_NP 
        (gamma, gamma') typeof_rec eval_rec)) as
        [[e1 e2] [[UP_e1 UP_e2] sound_e1]]; auto; simpl in *|-*.      
      destruct e as [e e_UP]; destruct e' as [e' e'_UP]; simpl.
      simpl in *|-*.
      revert sound_e1.
      unfold eval_alg_Soundness_P; simpl.
      repeat rewrite e_eq, e'_eq, e1_eq, e2_eq; simpl.
      intros sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0 T; 
        generalize (sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0  T); intros.
      unfold inject; simpl.
      rewrite wf_functor.
      erewrite wf_np; try apply H2; simpl; auto.
      erewrite wf_np; simpl; auto.
      unfold inject in H3; simpl in H3; rewrite wf_functor in H3; apply H3.
      destruct IHa as [a_eqv IHa]; destruct IHb as [b_eqv IHb]; destruct IHc as [c_eqv IHc].
      split; intros.
      apply inject_i; econstructor 4; eauto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV _ WF_eqv_environment_P
          (E (typeofR D)) (Fun_E (typeofR D)) 
          (gamma, gamma') typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig a, proj1_sig a')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      apply IHa; auto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV _ WF_eqv_environment_P
          (E (typeofR D)) (Fun_E (typeofR D)) 
          (gamma, gamma')  typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig b, proj1_sig b')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      apply IHb; auto.
      assert (UP'_P2
        (eval_alg_Soundness_P D V (E nat) WFV _ WF_eqv_environment_P
          (E (typeofR D)) (Fun_E (typeofR D)) 
          (gamma, gamma') typeof_rec eval_rec f_algebra f_algebra)
        (proj1_sig c, proj1_sig c')).
      unfold UP'_P2; intros.
      econstructor.
      instantiate (1 := conj (proj2_sig _) (proj2_sig _)).
      apply IHc; auto.
      generalize (proj1_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg 
        (gamma, gamma')) 
        (np _ (exist _ (proj1_sig a, proj1_sig a') H0)
          (exist _ (proj1_sig b, proj1_sig b') H1)
          (exist _ (proj1_sig c, proj1_sig c') H2))).
      generalize (proj2_eq (WF_Ind2 := WF_Ind_eval_Soundness_alg
        (gamma, gamma')) 
        (np _ (exist _ (proj1_sig a, proj1_sig a') H0)
          (exist _ (proj1_sig b, proj1_sig b') H1)
          (exist _ (proj1_sig c, proj1_sig c') H2))).
      simpl.
      intros e1_eq e2_eq.
      destruct (p_algebra (PAlgebra := eval_Soundness_alg_NP
        (gamma, gamma') typeof_rec eval_rec)) as
      [[e1 e2] [[UP_e1 UP_e2] sound_e1]]; auto; simpl in *|-*.      
      destruct e as [e e_UP]; destruct e' as [e' e'_UP]; simpl.
      simpl in *|-*.
      revert sound_e1.
      unfold eval_alg_Soundness_P; simpl.
      repeat rewrite e_eq, e'_eq, e1_eq, e2_eq; simpl.
      intros sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0 T; 
        generalize (sound_e1 eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa0 T); intros.
      unfold inject; simpl.
      rewrite wf_functor.
      erewrite wf_np; try apply H3; simpl; auto.
      erewrite wf_np; simpl; auto.
      unfold inject in H4; simpl in H4; rewrite wf_functor in H4; apply H4.
    Qed. 
    
    Context {eqv_eval_soundness_alg : forall typeof_rec eval_rec,
      iPAlgebra eqv_eval_SoundnessName 
      (eqv_eval_alg_Soundness'_P 
        typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := eval_E _))) (EQV_E _ _)}.

    Definition eqv_eval_soundness_P (i : eqv_i (typeofR D) nat) := 
      forall (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (env_B _ _ i) n = Some b -> 
          exists T, lookup (env_A _ _ i) b = Some T)
        (WF_gamma2 : List.length (env_A _ _ i) = List.length (env_B _ _ i))
        (WF_gamma' : forall n b, lookup (env_B _ _ i) n = Some b -> b = n) 
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (env_A _ _ i)) T,
        typeof _ _ (proj1_sig (eqv_a _ _ i)) = Some T -> 
        WFValueC _ _ WFV (eval (eval_E := eval_E) 
          V _ (proj1_sig (eqv_b _ _ i)) gamma'') T.

    Variable (WF_MAlg_typeof : WF_MAlgebra Typeof_E).
    Variable (WF_MAlg_eval : WF_MAlgebra eval_E).

    Lemma eqv_eval_soundness' : forall gamma gamma' e' e'',
      E_eqvC EQV_E gamma gamma' e' e'' -> 
      eqv_eval_soundness_P (mk_eqv_i _ _ gamma gamma' e' e'').
    Proof.
      intros; generalize (ifold_ (EQV_E _ _) _
        (ip_algebra (iPAlgebra := eqv_eval_soundness_alg 
          (fun e => typeof D (E (typeofR D)) (proj1_sig e)) 
          (fun e => eval V (E nat) (proj1_sig e)))) (mk_eqv_i _ _ gamma gamma' e' e'') H).
      unfold eqv_eval_alg_Soundness'_P, eqv_eval_soundness_P; simpl;
        intros.
      revert H1.
      destruct e' as [e' e'_UP]; destruct e'' as [e'' e''_UP]; 
        simpl in *|-*.
      rewrite <- (@in_out_UP'_inverse _ _ e'' _).
      simpl; unfold typeof, eval, fold_, mfold, in_t.
      rewrite wf_malgebra; unfold mfold.
      unfold eval_alg_Soundness_P in H0.
      intros; eapply H0; unfold WF_eqv_environment_P. 
      intro; rewrite (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig _)); reflexivity.
      intro; rewrite (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig _)); reflexivity.
      split; eauto.
      intros; simpl; unfold eval, mfold, in_t.
      rewrite wf_malgebra; eapply H2; eauto.
      rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig (fst a)) (proj2_sig _)) in H3.
      simpl in H3; unfold typeof, mfold, in_t in H3.
      rewrite <- wf_malgebra;  apply H3.
      rewrite <- (@in_out_inverse _ _ e' _) in H1; unfold in_t in H1.
      simpl; rewrite <- wf_malgebra.
      simpl; unfold out_t_UP'.
      rewrite Fusion with (g := (fmap in_t)). 
      apply H1.
      auto.
      intros; repeat rewrite fmap_fusion; reflexivity.
    Qed.

    Lemma eqv_eval_soundness : forall gamma gamma' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' -> 
      forall (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (gamma') n = Some b -> 
          exists T, lookup (gamma) b = Some T)
        (WF_gamma2 : List.length (gamma) = List.length (gamma'))
        (WF_gamma' : forall n b, lookup (gamma') n = Some b -> b = n) 
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (gamma)) T,
        typeof _ _ (proj1_sig e') = Some T -> 
        WFValueC _ _ WFV (eval (eval_E := eval_E) 
          V _ (proj1_sig (e'')) gamma'') T.
    Proof.
      intros; eapply eqv_eval_soundness'; eauto.
    Qed.

    Definition soundness_X'_P 
      (typeof_rec : Exp (E (typeofR D)) -> typeofR D)
      (eval_rec : Exp (E nat) -> evalR V)
      (typeof_F : Mixin (Exp (E (typeofR D))) (E (typeofR D)) (typeofR D))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalR V))
      i :=       
      forall (IH : forall (e : Exp _) (e' : Exp _)
        pb gamma'' (WF_gamma'' : WF_eqv_environment_P pb gamma'')
        T, 
        E_eqvC EQV_E (fst pb) (snd pb) e e' ->
        typeof_rec e = Some T -> 
        WFValueC _ _ WFV (eval_rec (in_t_UP' _ _ (out_t_UP' _ _ (proj1_sig e'))) gamma'') T),
      E_eqv EQV_E _ _ i /\
      eval_alg_Soundness_P D V (E nat) WFV 
      _ WF_eqv_environment_P
      (E (typeofR D)) _ (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec 
      typeof_F eval_F
      (proj1_sig (eqv_a _ _ i), proj1_sig (eqv_b _ _ i))
      (conj (proj2_sig (eqv_a _ _ i)) (proj2_sig (eqv_b _ _ i))).

    Inductive soundness_XName : Set := soundness_Xname.

    Global Instance Lift_soundness_X_alg 
      typeof_rec eval_rec typeof_alg eval_alg 
      EQV_G {fun_EQV_G : iFunctor EQV_G}
      {EQV_G_EQV_Alg : iPAlgebra eqv_eval_SoundnessName 
        (eqv_eval_alg_Soundness'_P typeof_rec eval_rec typeof_alg eval_alg) EQV_G} :
        iPAlgebra soundness_XName 
        (soundness_X'_P 
          typeof_rec eval_rec typeof_alg eval_alg) EQV_G.
      intros; econstructor; generalize (ip_algebra); unfold iAlgebra; intros.
      unfold soundness_X'_P; intros.
      assert (EQV_G (eqv_eval_alg_Soundness'_P typeof_rec eval_rec typeof_alg eval_alg) i).
      eapply ifmap; try eapply H0.
      intros; apply H1; apply IH.
      apply (H _ H1).
    Defined.
      
    Context {soundness_X_alg : forall eval_rec,
      iPAlgebra soundness_XName 
      (soundness_X'_P 
        (fun e => typeof _ _ (proj1_sig e)) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E))) (EQV_E _ _)}.
    Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.  

    Definition soundness_X_P (i : eqv_i (typeofR D) nat) := 
      forall n (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (env_B _ _ i) n = Some b -> 
          exists T, lookup (env_A _ _ i) b = Some T)
        (WF_gamma2 : List.length (env_A _ _ i) = List.length (env_B _ _ i))
        (WF_gamma' : forall n b, lookup (env_B _ _ i) n = Some b -> b = n) 
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (env_A _ _ i)) T,
        typeof _ _ (proj1_sig (eqv_a _ _ i)) = Some T -> 
        WFValueC _ _ WFV (beval V (E _) n (beval_E := beval_E) 
          (eqv_b _ _ i) gamma'') T.

    Lemma soundness_X' : 
      forall eval_rec gamma gamma' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' -> 
        soundness_X'_P (fun e => typeof _ _ (proj1_sig e)) eval_rec 
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E)) (mk_eqv_i _ _ gamma gamma' e' e'').
    Proof.
      intros; apply (ifold_ (EQV_E _ _ )); try assumption.
      apply ip_algebra.
    Qed.

    Variable SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop.
    Variable funSV : iFunctor SV.
    Variable Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV.
    Variable Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV.

    Context {WF_Value_continous_alg : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.
    Context {eval_continuous_Exp_E : PAlgebra EC_ExpName
      (sig (UP'_P (eval_continuous_Exp_P V (E _) SV))) (E nat)}.
    Context {WF_Ind_EC_Exp : WF_Ind eval_continuous_Exp_E}.

    Lemma soundness_X : 
      forall n gamma gamma' gamma'' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' -> 
        forall (WF_gamma : forall n b, lookup gamma' n = Some b -> 
          exists T, lookup gamma b = Some T)
        (WF_gamma2 : List.length gamma = List.length gamma')
        (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' gamma) T,
        typeof _ _ (proj1_sig e') = Some T -> 
        WFValueC _ _ WFV (beval V (E _) n (beval_E := beval_E) 
          e'' gamma'') T.
    Proof.
      induction n; simpl; 
          intros; unfold beval; simpl in *|-*.
      apply (inject_i (subGF := Sub_WFV_Bot_WFV)); econstructor; eauto.
      generalize (soundness_X' (beval V (E _) n) _ _ _ _ H).
      unfold soundness_X'_P; 
        unfold eval_alg_Soundness_P; simpl; intros.
      apply H1; auto.
      unfold beval; intros; erewrite bF_UP_in_out.
      instantiate (1 := proj2_sig _).
      destruct e'0; simpl; auto.
      destruct WF_gamma''0 as [WF_pb [WF_pb2 [WF_pb' WF_gamma''0]]].
      eapply IHn; eauto.
      intro; destruct e; unfold beval; erewrite bF_UP_in_out;
        auto.
      intro; rewrite <- (@in_out_UP'_inverse _ _ (proj1_sig e) (proj2_sig _)) at 1;
        reflexivity.
      repeat split; auto.
      intros.
      destruct a as [[a a_UP'] [a' a'_UP']].
      unfold beval; erewrite (@bF_UP_in_out _ _ _ _ _ _ _ a'_UP').
      apply (WF_Value_beval D V (E _) SV _ _ _ _ WFV n (S n) _ gamma''0); auto.
      apply Sub_Environment_refl; auto.
      unfold beval; simpl.
      simpl in H2.
      unfold beval in H2; apply H2.
      simpl in H3.
      unfold typeof in H3.
      rewrite <- (@in_out_UP'_inverse _ _ a a_UP') in H3.
      simpl in H3; unfold typeof, mfold, in_t in H3. 
      rewrite <- wf_malgebra; apply H3.
      rewrite <- wf_malgebra.
      rewrite <- (@in_out_UP'_inverse _ _ _ (proj2_sig e')) in H0.
      simpl in H0; unfold typeof, mfold, in_t in H0. 
      apply H0.
    Qed.

  End NP_beval_Soundness.
      
End PNames.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
