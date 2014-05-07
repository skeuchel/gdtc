Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.

Section Arith.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Arithmetic Type. *)
  Inductive AType (A : Set) : Set :=
  | TNat : AType A.

  Definition AType_fmap : forall (A B : Set) (f : A -> B), 
    AType A -> AType B := fun A B _ _ => TNat _.

  Global Instance AType_Functor : Functor AType :=
    {| fmap := AType_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_AType_D  : AType :<: D}.

   (* Constructor + Universal Property. *)
  Context {WF_Sub_AType_D : WF_Functor _ _ Sub_AType_D _ _}.
  
  Definition tnat' : DType := inject' (TNat _).
  Definition tnat : Fix D := proj1_sig tnat'. 
  Global Instance UP'_tnat : 
    Universal_Property'_fold tnat := proj2_sig tnat'.

  (* Induction Principle for Nat Types. *)
  Definition ind_alg_AType
    (P : forall d : Fix D, Universal_Property'_fold d -> Prop) 
    (H : UP'_P P tnat)
    (d : AType (sig (UP'_P P))) : sig (UP'_P P) :=
    match d with
      | TNat => exist _ _ H 
    end.

    Lemma WF_ind_alg_AType (Name : Set)
    (P : forall e : Fix D, Universal_Property'_fold e -> Prop) 
    (H : UP'_P P tnat)
    {Sub_AType_D' : AType :<: D} :
    (forall a, inj (Sub_Functor := Sub_AType_D) a =
      inj (A := Fix D) (Sub_Functor := Sub_AType_D') a) ->
      WF_Ind (Name := Name) {| p_algebra := fun H0 => ind_alg_AType P H H0|}.
      constructor; intros.
      simpl; unfold ind_alg_AType; destruct e; simpl.
      unfold tnat; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.
  
  (* Type Equality Section. *)
  Definition isTNat : Fix D -> bool :=
   fun typ =>
     match project typ with
      | Some TNat => true
      | None      => false
     end.

  Definition AType_eq_DType  (R : Set) (rec : R -> eq_DTypeR D) 
    (e : AType R) : eq_DTypeR D :=
    match e with 
      | TNat => fun t => isTNat (proj1_sig t)
    end.
  
  Global Instance MAlgebra_eq_DType_Arith T:
    FAlgebra eq_DTypeName T (eq_DTypeR D) AType :=
    {| f_algebra := AType_eq_DType T|}.

  Context {eq_DType_DT : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {WF_DType_eq_DT : forall T, @WF_FAlgebra eq_DTypeName T _ _ _
    Sub_AType_D (MAlgebra_eq_DType_Arith T) (eq_DType_DT _)}.

  Lemma AType_eq_DType_eq_H : UP'_P (eq_DType_eq_P D) tnat.
    unfold UP'_P; econstructor.
    unfold eq_DType_eq_P; intros.
    unfold eq_DType, mfold, tnat, tnat', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H. 
    rewrite (wf_algebra (WF_FAlgebra := WF_DType_eq_DT _)) in H; simpl in H.
    unfold isTNat in H.
    caseEq (project (proj1_sig d2)); rewrite H0 in H;
      try discriminate; destruct a.
    unfold project in H0.
    apply inj_prj in H0.
    unfold tnat, tnat'; simpl; rewrite wf_functor; simpl.
    unfold AType_fmap.
    generalize (f_equal (in_t_UP' _ _ ) H0); intros.
    apply (f_equal (@proj1_sig _ _)) in H1;
      rewrite in_out_UP'_inverse in H1.
    rewrite H1; simpl; rewrite wf_functor; simpl; unfold AType_fmap;
      reflexivity.
    exact (proj2_sig d2).
  Qed.

  Global Instance PAlgebra_eq_DType_eq_AType :
    PAlgebra eq_DType_eqName (sig (UP'_P (eq_DType_eq_P D))) AType.
  Proof.
    constructor; unfold Algebra; intros.
    eapply (ind_alg_AType (eq_DType_eq_P D) AType_eq_DType_eq_H H).
  Defined.
  
  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Arith (a : Set) : Set :=
  | Lit : nat -> Arith a
  | Add : a -> a -> Arith a.

  Definition Arith_fmap (B C : Set) (f : B -> C) (Aa : Arith B) : Arith C :=
    match Aa with 
      | Lit n => Lit _ n
      | Add a b => Add _ (f a) (f b)
    end.
      
  Global Instance Arith_Functor : Functor Arith :=
    {| fmap := Arith_fmap |}.
    destruct a; reflexivity.
    (* fmap id *)
    destruct a; reflexivity.
  Defined.

  Variable F : Set -> Set.
  Context {Fun_F : Functor F}.
  Definition Exp := Exp F.
  Context {Sub_Arith_F : Arith :<: F}.

  (* Constructor + Universal Property. *)
   Context {WF_Sub_Arith_F : WF_Functor _ _ Sub_Arith_F _ _}.
  Definition lit' (n : nat) : Exp := inject' (Lit _ n).
  Definition lit  (n : nat) : Fix F := proj1_sig (lit' n).
  Global Instance UP'_lit {n : nat} : 
    Universal_Property'_fold (lit n) := proj2_sig (lit' n).

  Definition add' (m n : Exp) : Exp :=  inject' (Add _ m n).

  Definition add (m n : Fix F) 
    {UP'_m : Universal_Property'_fold m}
    {UP'_n : Universal_Property'_fold n}
    : Fix F := proj1_sig (add' (exist _ _ UP'_m) (exist _ _ UP'_n)).

   Global Instance UP'_add {m n : Fix F} 
     {UP'_m : Universal_Property'_fold m}
     {UP'_n : Universal_Property'_fold n}
     :
     Universal_Property'_fold (add m n) :=
     proj2_sig (add' (exist _ _ UP'_m) (exist _ _ UP'_n)).

  (* Induction Principles for Arith. *)
  Definition ind_alg_Arith
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop) 
    (H : forall n, UP'_P P (lit n))
    (H0 : forall m n
      (IHm : UP'_P P m) 
      (IHn : UP'_P P n),
      UP'_P P (@add m n (proj1_sig IHm) (proj1_sig IHn)))
      (e : Arith (sig (UP'_P P))) 
        : 
        sig (UP'_P P) :=
    match e with
      | Lit n => exist _ (lit n) (H n)
      | Add m n => exist (UP'_P P) _
        (H0 (proj1_sig m) (proj1_sig n) (proj2_sig m) (proj2_sig n))
    end.

  Definition ind2_alg_Arith
    {E E' : Set -> Set}
    {Fun_E : Functor E}
    {Fun_E' : Functor E'}
    {Sub_Arith_E : Arith :<: E}
    {Sub_Arith_E' : Arith :<: E'}
    (P : forall e : (Fix E) * (Fix E'), 
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop) 
    (H : forall n, UP'_P2 P (inject (Lit _ n), inject (Lit _ n)))
    (H0 : forall m n
      (IHm : UP'_P2 P m) 
      (IHn : UP'_P2 P n),
      UP'_P2 P (inject (Add _ (exist _ _ (proj1 (proj1_sig IHm))) 
        (exist _ _ (proj1 (proj1_sig IHn)))),
      inject (Add _ (exist _ _ (proj2 (proj1_sig IHm))) 
        (exist _ _ (proj2 (proj1_sig IHn))))))
      (e : Arith (sig (UP'_P2 P))) 
        : 
        sig (UP'_P2 P) :=
    match e with
      | Lit n => exist _ _ (H n)
      | Add m n => exist (UP'_P2 P) _
        (H0 (proj1_sig m) (proj1_sig n) (proj2_sig m) (proj2_sig n))
    end.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Arithmetic Expressions. *)

  Definition Arith_typeof (R : Set) (rec : R -> typeofR D) 
     (e : Arith R) : typeofR D := 
     match e with 
       | Lit n => Some (inject' (TNat _))
       | Add m n => match (rec m), (rec n) with 
                      | Some T1, Some T2 => 
                        match isTNat (proj1_sig T1), isTNat (proj1_sig T2) with
                          | true, true => Some (inject' (TNat _))
                          | _, _ => None
                        end
                      | _, _ => None
                    end
     end.

  Global Instance MAlgebra_typeof_Arith T:
    FAlgebra TypeofName T (typeofR D) Arith :=
    {| f_algebra := Arith_typeof T|}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (* Arithmetic Values. *)
   Inductive NatValue (A : Set) : Set :=
   | VI : nat -> NatValue A.
   
   Definition VI_fmap : forall (A B : Set) (f : A -> B), 
     NatValue A -> NatValue B := 
     fun A B _ e => match e with 
                      | VI n => VI _ n
                    end.

   Global Instance VI_Functor : Functor NatValue :=
     {| fmap := VI_fmap |}.
     destruct a; reflexivity.
     destruct a; reflexivity.
   Defined.

   Variable V : Set -> Set.
   Context {Fun_V : Functor V}.
   Definition Value := Value V.
   Context {Sub_NatValue_V : NatValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_NatValue_F : WF_Functor _ _ Sub_NatValue_V _ _}.

  Definition vi' (n : nat) : Value := inject' (VI _ n).
  Definition vi (n : nat) : Fix V := proj1_sig (vi' n).

   Global Instance UP'_vi {n : nat} : 
     Universal_Property'_fold (vi n) := proj2_sig (vi' n).

   (* Constructor Testing for Arithmetic Values. *)

   Definition isVI : Fix V -> option nat :=
     fun exp =>
       match project exp with
        | Some (VI n) => Some n
        | None        => None
       end.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck' : nat -> Value := stuck' _.
   Definition stuck : nat -> Fix V := stuck _.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Context {Sub_BotValue_V : BotValue :<: V}.

   (* Evaluation Algebra for Arithemetic Expressions. *)
  
   Definition Arith_eval (R : Set) (rec : R -> evalR V) 
     (e : Arith R) : evalR V :=
       match e with 
         | Lit n => (fun _ => vi' n)
         | Add m n => (fun env => 
           let m' := (rec m env) in
             let n' := (rec n env) in
               match isVI (proj1_sig m'), isVI (proj1_sig n') with 
                 | Some m', Some n' => vi' (m' + n')
                 | _, _ => 
                   if @isBot _ Fun_V Sub_BotValue_V (proj1_sig m') then @bot' _ Fun_V Sub_BotValue_V else
                     if @isBot _ Fun_V Sub_BotValue_V (proj1_sig n') then @bot' _ Fun_V Sub_BotValue_V else 
                       stuck' 4
               end)
       end.

  Global Instance MAlgebra_eval_Arith T :
    FAlgebra EvalName T (evalR V) Arith :=
    {| f_algebra := Arith_eval T |}.


  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  (* Pretty Printing Functions*)

  Require Import Ascii.
  Require Import String.
  
  Global Instance MAlgebra_DTypePrint_AType T:
    FAlgebra DTypePrintName T DTypePrintR AType :=
    {| f_algebra := fun rec e => append "tnat" "" |}.

  Global Instance MAlgebra_ExpPrint_Arith T :
    FAlgebra ExpPrintName T (ExpPrintR) Arith :=
    {| f_algebra := fun rec e => match e with 
      | Lit n => fun i => String (ascii_of_nat (n + 48)) EmptyString
      | Add m n => fun i => append "(" ((rec m i) ++ " + " ++ (rec n i) ++ ")")
    end |}.

  Global Instance MAlgebra_ValuePrint_AType T :
    FAlgebra ValuePrintName T ValuePrintR NatValue :=
    {| f_algebra := fun rec e => 
      match e with 
        | VI n => String (ascii_of_nat (n + 48)) EmptyString
      end |}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName Exp (evalR V) F}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ Arith F
    Sub_Arith_F (MAlgebra_eval_Arith _) eval_F}.

   (* Continuity of Evaluation. *)

  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V Bot_Functor Fun_V}.
  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

  (* Lit case. *)

  Ltac WF_FAlg_rewrite := repeat rewrite wf_functor; simpl;
    repeat rewrite out_in_fmap; simpl; 
      repeat rewrite wf_functor; simpl;
        repeat rewrite wf_algebra; simpl.

    Lemma eval_continuous_Exp_H : forall n, 
      UP'_P (eval_continuous_Exp_P V F SV) (lit n).
      unfold eval_continuous_Exp_P; intros; econstructor; intros.
      unfold beval, mfold, lit; simpl; unfold inject.
      WF_FAlg_rewrite.
      apply inject_i.
      constructor.
      reflexivity.
    Qed.

    (* Add case. *)

    Context {Dis_VI_Bot : Distinct_Sub_Functor _ Sub_NatValue_V Sub_BotValue_V}.

    (* Inversion principles for natural number SubValues. *)
    Definition SV_invertVI_P (i : SubValue_i V) := 
      forall n, proj1_sig (sv_a _ i) = vi n -> 
        proj1_sig (sv_b _ i) = vi n.

    Inductive SV_invertVI_Name := ece_invertvi_name.
    Context {SV_invertVI_SV :
      iPAlgebra SV_invertVI_Name SV_invertVI_P SV}.    

    Global Instance SV_invertVI_refl : 
      iPAlgebra SV_invertVI_Name SV_invertVI_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVI_P.
      inversion H; subst; simpl; congruence.
    Defined.

    Lemma SV_invertVI_default : forall V' 
      (Fun_V' : Functor V')
      (SV' : (SubValue_i V -> Prop) -> SubValue_i V -> Prop)
      (sub_V'_V : V' :<: V)
      (WF_V' : WF_Functor V' V sub_V'_V Fun_V' Fun_V),
      (forall (i : SubValue_i V) (H : SV' SV_invertVI_P i), 
        exists v', proj1_sig (sv_a _ i) = inject v') -> 
      Distinct_Sub_Functor _ Sub_NatValue_V sub_V'_V -> 
      iPAlgebra SV_invertVI_Name SV_invertVI_P SV'.
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVI_P.
      destruct (H _ H1) as [v' eq_v'].
      intros; rewrite eq_v' in H2.
      elimtype False.
      unfold vi, inject, vi', inject' in H2; simpl in H2.
      apply sym_eq in H2.
      apply (inject_discriminate H0 _ _ H2).
    Defined.

    Global Instance SV_invertVI_Bot : 
      iPAlgebra SV_invertVI_Name SV_invertVI_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVI_P.
      inversion H; subst; simpl; intros.
      elimtype False.
      rewrite H0 in H1.
      unfold vi, inject, vi', inject' in H1; simpl in H1.
      repeat rewrite out_in_inverse, wf_functor in H1; simpl in H1.
      eapply (inject_discriminate Dis_VI_Bot); unfold inject; simpl; eauto.
    Defined.

    Context {iFun_F : iFunctor SV}.
    Definition SV_invertVI := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertVI_SV)).

    Definition SV_invertVI'_P (i : SubValue_i V) := 
      forall n, proj1_sig (sv_b _ i) = vi n -> 
        proj1_sig (sv_a _ i) = vi n \/ proj1_sig (sv_a _ i) = bot _.

    Inductive SV_invertVI'_Name := ece_invertvi'_name.
    Context {SV_invertVI'_SV :
      iPAlgebra SV_invertVI'_Name SV_invertVI'_P SV}.    

    Global Instance SV_invertVI'_refl : 
      iPAlgebra SV_invertVI'_Name SV_invertVI'_P (SubValue_refl V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVI'_P.
      inversion H; subst; simpl; eauto.
      intros.
      left; congruence.
    Defined.

    Global Instance SV_invertVI'_Bot : 
      iPAlgebra SV_invertVI'_Name SV_invertVI'_P (SubValue_Bot V).
      econstructor; intros.
      unfold iAlgebra; intros; unfold SV_invertVI'_P.
      inversion H; subst; simpl; eauto.
    Defined.

    Definition SV_invertVI' := ifold_ SV _ (ip_algebra (iPAlgebra := SV_invertVI'_SV)).

    (* End Inversion principles for SubValue.*)
    
    Context {SV_invertBot_SV :
      iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.

    Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.

    Lemma project_bot_vi : forall n, 
      project (F := V) (G := BotValue) (vi n) = None.
    Proof. 
      intros; unfold project, vi; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold VI_fmap.
      caseEq (prj (sub_F := BotValue) (inj (sub_G := V) (VI (sig (@Universal_Property'_fold V _)) n))).
      apply inj_prj in H; elimtype False; eapply (inject_discriminate Dis_VI_Bot);
        unfold inject; repeat apply f_equal; apply H.
      auto.
    Qed.

    Lemma project_vi_bot : project (F := V) (G := NatValue) (bot _) = None.
    Proof. 
      intros; unfold project, bot; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold Bot_fmap.
      caseEq (prj (sub_F := NatValue) (inj (sub_G := V) (Bot (sig (@Universal_Property'_fold V _))))).
      apply inj_prj in H; elimtype False; eapply (inject_discriminate Dis_VI_Bot);
        unfold inject; repeat apply f_equal; apply sym_eq in H; apply H.
      auto.
    Qed.

    Lemma project_vi_vi : forall n, 
      project (F := V) (G := NatValue) (vi n) = Some (VI _ n).
    Proof. 
      intros; unfold project, vi, inject; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold VI_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

    Lemma eval_continuous_Exp_H0 : forall 
      (m n : Fix F)
      (IHm : UP'_P (eval_continuous_Exp_P V F SV) m) 
      (IHn : UP'_P (eval_continuous_Exp_P V F SV) n), 
      UP'_P (eval_continuous_Exp_P V F SV) (@add m n (proj1_sig IHm) (proj1_sig IHn)).
      unfold eval_continuous_Exp_P; intros.
      destruct IHm as [m_UP' IHm].
      destruct IHn as [n_UP' IHn].
      econstructor; intros; eauto with typeclass_instances.
      unfold beval, mfold, add; simpl.
      unfold inject; simpl; repeat rewrite out_in_fmap; simpl; 
        repeat rewrite wf_functor; simpl.
      repeat rewrite (wf_algebra (WF_FAlgebra := WF_eval_F)); simpl.
      repeat erewrite bF_UP_in_out.
      caseEq (project (G := NatValue) 
        (proj1_sig (boundedFix_UP m0 f_algebra
          (fun _ : Env (Names.Value V) => bot' V)
          (exist Universal_Property'_fold m m_UP') gamma))).
      unfold isVI at 1, evalR, Names.Exp; rewrite H2.
      destruct n1.
      generalize (H (exist _ m m_UP') _ _ _ H0 H1); simpl; intros.
      generalize (inj_prj _ _ H2); rename H2 into H2'; intros.
      assert (proj1_sig
            (boundedFix_UP m0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold m m_UP') gamma) = vi n1) as Eval_m. 
      unfold vi, vi', inject'; rewrite <- H2; rewrite in_out_UP'_inverse; eauto.
      exact (proj2_sig _).
      clear H2; rename H3 into SubV_m.
      unfold isVI; unfold eval, mfold in SubV_m.
      caseEq (project (G := NatValue) (proj1_sig
              (boundedFix_UP m0 f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold n n_UP') gamma))).
      destruct n2.
      generalize (H (exist _ n n_UP') _ _ _ H0 H1); simpl; intros.
      generalize (inj_prj _ _ H2); rename H2 into H3'; intros.
      assert (proj1_sig
            (boundedFix_UP m0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold n n_UP') gamma) = vi n2) as Eval_n. 
      unfold vi, vi', inject'; rewrite <- H2; rewrite in_out_UP'_inverse; eauto.
      exact (proj2_sig _).
      clear H2; rename H3 into SubV_n.
      unfold isVI; unfold eval, mfold in SubV_n.
      generalize (SV_invertVI _ SubV_m _ Eval_m).
      generalize (SV_invertVI _ SubV_n _ Eval_n).
      simpl; unfold beval at 1; unfold beval at 1; unfold evalR, Names.Exp; intros.
      rewrite H3, H2.
      unfold project, vi, vi'; simpl; repeat rewrite out_in_fmap;
        repeat rewrite wf_functor; repeat rewrite prj_inj;
          repeat rewrite wf_functor; simpl.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
      unfold isBot; rewrite Eval_m.
      caseEq (project (G := BotValue) (vi n1)).
      destruct b; generalize (inj_prj _ _ H3); intro. 
      assert (vi n1 = bot _) by
        (unfold vi, vi', bot, bot', inject' at -1; rewrite <- H4;
          rewrite in_out_UP'_inverse; eauto with typeclass_instances).
      unfold vi, bot in H5.
      elimtype False; eapply (inject_discriminate Dis_VI_Bot _ _ H5).
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP m0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold n n_UP') gamma))).
      destruct b.
      apply inject_i; constructor; reflexivity.
      generalize (H (exist _ n n_UP') _ _ _ H0 H1) as SubV_n; simpl; intros.
      caseEq (project (G := NatValue)
           (proj1_sig
              (boundedFix_UP n0 f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold m m_UP') gamma'))).
      destruct n2.
      caseEq (project (G := NatValue)
           (proj1_sig
              (boundedFix_UP n0 f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold n n_UP') gamma'))).
      destruct n3.
      generalize (inj_prj _ _ H5); rename H5 into H5'; intros.
      assert (proj1_sig
            (boundedFix_UP n0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold m m_UP') gamma') = vi n2) as Eval_m' by 
        (unfold vi, vi', inject'; rewrite <- H5;
          rewrite in_out_UP'_inverse; unfold eval, mfold; eauto;
            exact (proj2_sig _)).
      unfold beval in SubV_m.
      generalize (inj_prj _ _ H6); rename H6 into H6'; intros.
      assert (proj1_sig
            (boundedFix_UP n0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold n n_UP') gamma') = vi n3) as Eval_n'.
      unfold vi, vi', inject'.
        (unfold vi, vi', inject'; rewrite <- H6;
          rewrite in_out_UP'_inverse; unfold eval, mfold; eauto;
            exact (proj2_sig _)).
      destruct (SV_invertVI' _ SubV_n _ Eval_n') as [n_eq_vi | n_eq_bot];
        simpl in *|-.
      unfold beval, mfold, evalR, Names.Exp in n_eq_vi; rewrite n_eq_vi in H2.
      unfold vi, project, inject in H2; simpl in H2; rewrite 
        out_in_fmap in H2.
      rewrite fmap_fusion in H2; rewrite wf_functor in H2; simpl in H2.
      rewrite (prj_inj _ ) in H2; discriminate.
      unfold beval, mfold, evalR, Names.Exp in n_eq_bot; rewrite n_eq_bot in H4.
      unfold bot, project, inject in H4; simpl in H4; rewrite out_in_fmap in H4.
      rewrite fmap_fusion, wf_functor in H4; simpl in H4.
      rewrite (prj_inj _ ) in H4; discriminate.
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n0 f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold m m_UP') gamma'))).
      destruct b.
      generalize (inj_prj _ _ H7); rename H7 into H7'; intros.
      assert (proj1_sig
        (beval _ _ n0 (exist Universal_Property'_fold m m_UP') gamma') = bot _ ) as Eval_m' by
      (apply (f_equal (in_t_UP' _ _)) in H7; apply (f_equal (@proj1_sig _ _)) in H7;
        rewrite in_out_UP'_inverse in H7; [apply H7 | exact (proj2_sig _)]).
      generalize (SV_invertBot _ SV _ _ SubV_m Eval_m'); simpl; intro H8;
        unfold beval, mfold, evalR, Names.Exp in H8; rewrite H8 in Eval_m.
      elimtype False; eapply (inject_discriminate Dis_VI_Bot (VI _ n1)); eauto.
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP n0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold n n_UP') gamma'))).
      destruct b.
      generalize (inj_prj _ _ H8); rename H8 into H8'; intros.
      assert (proj1_sig
        (beval _ _ n0 (exist Universal_Property'_fold n n_UP') gamma') = bot _ ) as Eval_n' by
      (apply (f_equal (in_t_UP' _ _)) in H8; apply (f_equal (@proj1_sig _ _)) in H8;
        rewrite in_out_UP'_inverse in H8; [apply H8 | exact (proj2_sig _)]).
      generalize (SV_invertBot _ SV _ _ SubV_n Eval_n'); simpl; intro H9;
        unfold beval, mfold, evalR, Names.Exp in H9. rewrite H9 in H4.
      unfold project, bot, bot' in H4; simpl in H4; rewrite out_in_fmap in H4;
        simpl in H4; repeat rewrite wf_functor in H4; simpl in H4;
          rewrite prj_inj in H4; discriminate.
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n0 f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold m m_UP') gamma'))).
      destruct b.
      unfold project in H6.
      apply inj_prj in H6; apply (f_equal (in_t_UP' _ _)) in H6; 
        apply (f_equal (@proj1_sig _ _)) in H6.
      rewrite in_out_UP'_inverse in H6; simpl.
      generalize (SV_invertBot _ SV _ _ SubV_m H6); simpl; intro.
      unfold beval, evalR, Names.Exp in H7; rewrite H7 in Eval_m.
      elimtype False; eapply (inject_discriminate Dis_VI_Bot (VI _ n1)); eauto.
      exact (proj2_sig _).
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n0 f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold n n_UP') gamma'))).
      destruct b.
      unfold project in H7.
      apply inj_prj in H7; apply (f_equal (in_t_UP' _ _)) in H7; 
        apply (f_equal (@proj1_sig _ _)) in H7.
      rewrite in_out_UP'_inverse in H7; simpl.
      generalize (SV_invertBot _ SV _ _ SubV_n H7); simpl; intro.
      unfold beval, evalR, Names.Exp in H8; rewrite H8 in H4.
      unfold project, bot, bot' in H4; simpl in H4; rewrite out_in_fmap in H4;
        simpl in H4; repeat rewrite wf_functor in H4; simpl in H4;
          rewrite prj_inj in H4; discriminate.
      exact (proj2_sig _).
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
      unfold isVI, evalR, Names.Exp; rewrite H2.
      unfold isBot.
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP m0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold m m_UP') gamma))).
      destruct b.
      apply inj_prj in H3; apply (f_equal (in_t_UP' _ _)) in H3; 
        apply (f_equal (@proj1_sig _ _)) in H3.
      assert (proj1_sig
            (boundedFix_UP m0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold m m_UP') gamma) = bot _) as Eval_m. 
      unfold bot, bot', inject'; rewrite <- H3; rewrite in_out_UP'_inverse; eauto.
      exact (proj2_sig _).
      apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP m0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold n n_UP') gamma))).
      destruct b.
      apply inj_prj in H4; apply (f_equal (in_t_UP' _ _)) in H4; 
        apply (f_equal (@proj1_sig _ _)) in H4.
      assert (proj1_sig
            (boundedFix_UP m0 f_algebra
               (fun _ : Env (Names.Value V) => bot' V)
               (exist Universal_Property'_fold n n_UP') gamma) = bot _) as Eval_n. 
      unfold bot, bot', inject'; rewrite <- H4; rewrite in_out_UP'_inverse; eauto.
      exact (proj2_sig _).
      apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP n0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold n n_UP') gamma))).
      rename H5 into Eval_n.
      unfold isVI; unfold eval, mfold in Eval_n.
      apply inj_prj in Eval_n; apply (f_equal (in_t_UP' _ _)) in Eval_n; 
        apply (f_equal (@proj1_sig _ _)) in Eval_n.
      rewrite in_out_UP'_inverse in Eval_n.
      caseEq (project (G := NatValue)
           (proj1_sig
              (boundedFix_UP n0 f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold m m_UP') gamma'))).
      generalize (H (exist _ m m_UP') _ _ _ H0 H1) as SubV_m; intros.
      destruct n1.
      apply inj_prj in H5; apply (f_equal (in_t_UP' _ _)) in H5; 
        apply (f_equal (@proj1_sig _ _)) in H5; 
          rewrite in_out_UP'_inverse in H5; 
            unfold beval, evalR, Names.Exp in SubV_m, H5.
      destruct (SV_invertVI' _ SubV_m _ H5); simpl in H6.
      rewrite H6 in H2; unfold project, vi, vi' in H2; simpl in H2.
      rewrite out_in_fmap in H2; repeat rewrite wf_functor in H2.
      rewrite prj_inj in H2; discriminate. 
      rewrite H6 in H3; unfold project, bot, bot' in H3; simpl in H3.
      rewrite out_in_fmap in H3; repeat rewrite wf_functor in H3.
      rewrite prj_inj in H3; discriminate. 
      exact (proj2_sig _).
      caseEq (project (G := BotValue)
             (proj1_sig
                (boundedFix_UP n0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold m m_UP') gamma'))).
      unfold evalR, Names.Exp in Eval_n.
      destruct b0.
      apply inj_prj in H6; apply (f_equal (in_t_UP' _ _)) in H6; 
        apply (f_equal (@proj1_sig _ _)) in H6;
          rewrite in_out_UP'_inverse in H6.
      generalize (H (exist _ m m_UP') _ _ _ H0 H1) as SubV_m; intros.
      unfold beval, evalR, Names.Exp in SubV_m, H6.
      generalize (SV_invertBot _ _ _ _ SubV_m H6); simpl;
        intros; rewrite H7 in H3.
      unfold project, bot, bot' in H3; simpl in H3.
      rewrite out_in_fmap in H3; repeat rewrite wf_functor in H3.
      rewrite prj_inj in H3; discriminate. 
      exact (proj2_sig _).
      caseEq (project  (G := BotValue) (proj1_sig
                (boundedFix_UP n0 f_algebra
                   (fun _ : Env (Names.Value V) => bot' V)
                   (exist Universal_Property'_fold n n_UP') gamma'))).
      destruct b0.
      apply inj_prj in H7; apply (f_equal (in_t_UP' _ _)) in H7; 
        apply (f_equal (@proj1_sig _ _)) in H7;
          rewrite in_out_UP'_inverse in H7.
      generalize (H (exist _ n n_UP') _ _ _ H0 H1) as SubV_n; intros.
      unfold beval, evalR, Names.Exp in SubV_n, H7.
      generalize (SV_invertBot _ _ _ _ SubV_n H7); simpl;
        intros; rewrite H8 in H4.
      unfold project, bot, bot' in H4; simpl in H4.
      rewrite out_in_fmap in H4; repeat rewrite wf_functor in H4.
      rewrite prj_inj in H4; discriminate. 
      exact (proj2_sig _).
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
      exact (proj2_sig _).
      caseEq (project (G := NatValue)
           (proj1_sig
              (boundedFix_UP n0 f_algebra
                 (fun _ : Env (Names.Value V) => bot' V)
                 (exist Universal_Property'_fold m m_UP') gamma'))).
      destruct n1.
      generalize (H (exist _ m m_UP') _ _ _ H0 H1) as SubV_m; intros.
      apply inj_prj in H6; apply (f_equal (in_t_UP' _ _)) in H6; 
        apply (f_equal (@proj1_sig _ _)) in H6; 
          rewrite in_out_UP'_inverse in H6; 
            unfold beval, evalR, Names.Exp in SubV_m, H6.
      destruct (SV_invertVI' _ SubV_m _ H6); simpl in H7.
      rewrite H7 in H2; unfold project, vi, vi' in H2; simpl in H2.
      rewrite out_in_fmap in H2; repeat rewrite wf_functor in H2.
      rewrite prj_inj in H2; discriminate. 
      rewrite H7 in H3; unfold project, bot, bot' in H3; simpl in H3.
      rewrite out_in_fmap in H3; repeat rewrite wf_functor in H3.
      rewrite prj_inj in H3; discriminate. 
      exact (proj2_sig _).
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n0 f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold m m_UP') gamma'))).
      destruct b.
      generalize (H (exist _ m m_UP') _ _ _ H0 H1) as SubV_m; intros.
      apply inj_prj in H7; apply (f_equal (in_t_UP' _ _)) in H7; 
        apply (f_equal (@proj1_sig _ _)) in H7; 
          rewrite in_out_UP'_inverse in H7; 
            unfold beval, evalR, Names.Exp in SubV_m, H7.
      generalize (SV_invertBot _ _ _ _ SubV_m H7); simpl; 
        intros.
      rewrite H8 in H3; unfold project, bot, bot' in H3; simpl in H3.
      rewrite out_in_fmap in H3; repeat rewrite wf_functor in H3.
      rewrite prj_inj in H3; discriminate.
      exact (proj2_sig _). 
      caseEq (project (G := BotValue)
        (proj1_sig
          (boundedFix_UP n0 f_algebra
            (fun _ : Env (Names.Value V) => bot' V)
            (exist Universal_Property'_fold n n_UP') gamma'))).
      destruct b.
      generalize (H (exist _ n n_UP') _ _ _ H0 H1) as SubV_n; intros.
      apply inj_prj in H8; apply (f_equal (in_t_UP' _ _)) in H8; 
        apply (f_equal (@proj1_sig _ _)) in H8; 
          rewrite in_out_UP'_inverse in H8; 
            unfold beval, evalR, Names.Exp in SubV_n, H8.
      generalize (SV_invertBot _ _ _ _ SubV_n H8); simpl; 
        intros.
      rewrite H9 in H4; unfold project, bot, bot' in H4; simpl in H4.
      rewrite out_in_fmap in H4; repeat rewrite wf_functor in H4.
      rewrite prj_inj in H4; discriminate.
      exact (proj2_sig _). 
      apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    Qed.

    Lemma project_bot_bot : project (F := V) (G := BotValue) (bot _) = Some (Bot _).
    Proof. 
      intros; unfold project, bot; simpl; rewrite out_in_fmap.
      repeat rewrite wf_functor; simpl; unfold Bot_fmap.
      rewrite prj_inj; reflexivity.
    Qed.

    Global Instance Arith_eval_continuous_Exp  : 
      PAlgebra EC_ExpName (sig (UP'_P (eval_continuous_Exp_P V F SV))) Arith.
    Proof.
      constructor; unfold Algebra; intros.
      eapply ind_alg_Arith.
      apply eval_continuous_Exp_H.
      apply eval_continuous_Exp_H0.
      assumption.
    Defined.

    Lemma WF_ind_alg_Arith (Name : Set)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop) 
    (H : forall n, UP'_P P (lit n))
    (H0 : forall m n
      (IHm : UP'_P P m) 
      (IHn : UP'_P P n),
      UP'_P P (@add m n (proj1_sig IHm) (proj1_sig IHn))) 
    {Sub_Arith_F' : Arith :<: F} :
    (forall a, inj (Sub_Functor := Sub_Arith_F) a =
      inj (A := (Fix F)) (Sub_Functor := Sub_Arith_F') a) ->
      WF_Ind (Name := Name) {| p_algebra := ind_alg_Arith P H H0|}.
      constructor; intros.
      simpl; unfold ind_alg_Arith; destruct e; simpl.
      unfold lit; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
      unfold add; simpl; rewrite wf_functor; simpl; apply f_equal; eauto.
    Defined.

    Context {eval_continuous_Exp_E : PAlgebra EC_ExpName
      (sig (UP'_P (eval_continuous_Exp_P V F SV))) F}.
    Context {WF_Ind_EC_Exp : WF_Ind eval_continuous_Exp_E}.

  (* ============================================== *)
  (* WELL-FORMED NAT VALUES                         *)
  (* ============================================== *)

    Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
    Variable funWFV : iFunctor WFV.

    (** Natrual Numbers are well-formed **)

    Inductive WFValue_VI (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop := 
    | WFV_VI : forall n v T, 
      proj1_sig v = vi n -> 
      proj1_sig T = tnat -> 
      WFValue_VI WFV (mk_WFValue_i D V v T).

    Definition ind_alg_WFV_VI (P : WFValue_i D V -> Prop) 
      (H : forall n v T veq Teq, P (mk_WFValue_i _ _ v T))
      i (e : WFValue_VI P i) : P i :=
      match e in WFValue_VI _ i return P i with
        | WFV_VI n v T veq Teq => H n v T veq Teq
      end.

    Definition WFV_VI_ifmap (A B : WFValue_i D V -> Prop) i (f : forall i, A i -> B i) 
      (WFV_a : WFValue_VI A i) : WFValue_VI B i :=
      match WFV_a in (WFValue_VI _ s) return (WFValue_VI B s)
        with
        | WFV_VI n v T veq Teq => WFV_VI B n v T veq Teq
      end.

    Global Instance iFun_WFV_VI : iFunctor WFValue_VI.
      constructor 1 with (ifmap := WFV_VI_ifmap).
      destruct a; simpl; intros; reflexivity.
      destruct a; simpl; intros; reflexivity.
    Defined.

    Variable Sub_WFV_VI_WFV : Sub_iFunctor WFValue_VI WFV.

     Global Instance WFV_proj1_a_VI : 
       iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFValue_VI.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_a_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; simpl; eauto.
       rewrite H3; eauto.
     Defined.

     Global Instance WFV_proj1_b_VI : 
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFValue_VI.
       econstructor; intros.
       unfold iAlgebra; intros; unfold WFV_proj1_b_P.
       inversion H; subst; simpl; intros.
       apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; simpl; eauto.
       rewrite H3; eauto.
     Defined.

    (* Inversion principles for Well-formed natural numbers. *)
    Definition WF_invertVI_P (i : WFValue_i D V) := 
      proj1_sig (wfv_b _ _ i) = tnat ->
      WFValue_VI (iFix WFV) i \/ (proj1_sig (wfv_a D V i) = bot V).

    Inductive WF_invertVI_Name := wfv_invertvi_name.
    Context {WF_invertVI_WFV :
      iPAlgebra WF_invertVI_Name WF_invertVI_P WFV}.    

    Global Instance WF_invertVI_VI : 
      iPAlgebra WF_invertVI_Name WF_invertVI_P WFValue_VI.
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertVI_P.
      inversion H; subst; simpl; intros.
      left; econstructor; eassumption.
    Defined.

    Global Instance WF_invertVI_Bot : 
      iPAlgebra WF_invertVI_Name WF_invertVI_P (WFValue_Bot _ _).
      econstructor; intros.
      unfold iAlgebra; intros; unfold WF_invertVI_P.
      inversion H; subst; simpl; intros.
      inversion H; subst; rewrite H3; right; reflexivity.
    Defined.

    Definition WF_invertVI := ifold_ WFV _ (ip_algebra (iPAlgebra := WF_invertVI_WFV)).

    Context {WFV_proj1_a_WFV :
      iPAlgebra WFV_proj1_a_Name (WFV_proj1_a_P D V WFV) WFV}.    
    Context {WFV_proj1_b_WFV :
       iPAlgebra WFV_proj1_b_Name (WFV_proj1_b_P D V WFV) WFV}. 

    Lemma Arith_eval_Soundness_H 
      (typeof_R eval_R : Set) typeof_rec eval_rec
      {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
      {WF_eval_F' : @WF_FAlgebra EvalName _ _ Arith F
        Sub_Arith_F (MAlgebra_eval_Arith _) (eval_F')} : 
      forall n : nat,
        forall gamma'' : Env (Names.Value V),
          forall T : Names.DType D,
            Arith_typeof typeof_R typeof_rec (Lit _ n) = Some T ->
            WFValueC D V WFV (Arith_eval eval_R eval_rec (Lit _ n) gamma'') T.
      intros n gamma'' T H4; intros.
      apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
      simpl.
      unfold vi, vi', inject; simpl; eauto.
      unfold typeof, mfold, lit in H4; simpl in H4.
      injection H4; intros; subst.
      reflexivity.
    Defined.

   Lemma Arith_eval_Soundness_H0 
     (typeof_R eval_R : Set) typeof_rec eval_rec
     {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
     {WF_eval_F' : @WF_FAlgebra EvalName _ _ Arith F
        Sub_Arith_F (MAlgebra_eval_Arith _) (eval_F')} : 
      forall (a b : typeof_R) (a' b' : eval_R),
        forall gamma'' : Env (Names.Value V),
          (forall T : Names.DType D,
            typeof_rec a = Some T ->
            WFValueC D V WFV (eval_rec a' gamma'') T) ->
          (forall T : Names.DType D,
            typeof_rec b = Some T ->
            WFValueC D V WFV (eval_rec b' gamma'') T) -> 
          forall T : Names.DType D,
            Arith_typeof typeof_R typeof_rec (Add _ a b) = Some T ->
            WFValueC D V WFV (Arith_eval eval_R eval_rec (Add _ a' b') gamma'') T.
     simpl; intros a b a' b' gamma'' IH_a IH_b T H4.
      caseEq (typeof_rec a); intros; rename H into typeof_a; 
        unfold typeofR in typeof_a, H4; rewrite typeof_a in H4; 
          try discriminate.
      caseEq (typeof_rec b); intros; rename H into typeof_b; 
        unfold typeofR in typeof_b, H4; rewrite typeof_b in H4; 
          try discriminate.
      caseEq (isTNat (proj1_sig d)); intros; rename H into d_eq; rewrite 
        d_eq in H4; try discriminate.
      caseEq (isTNat (proj1_sig d0)); intros; rename H into d0_eq; rewrite 
        d0_eq in H4; try discriminate.
      injection H4; intros; subst; clear H4.
      unfold isTNat in d_eq, d0_eq.
      caseEq (project (proj1_sig d)); intros; rewrite H in d_eq; 
        try discriminate; clear d_eq; rename H into d_eq; destruct a0.
      caseEq (project (proj1_sig d0)); intros; rewrite H in d0_eq; 
        try discriminate; clear d0_eq; rename H into d0_eq; destruct a0.
      apply project_inject in d_eq; apply project_inject in d0_eq; 
        eauto with typeclass_instances.
      generalize (IH_a _ typeof_a) as WF_a;
      generalize (IH_b _ typeof_b) as WF_b; intros.
      unfold WFValueC in *|-*.
      destruct (WF_invertVI _ WF_a d_eq) as [beval_a' | beval_a']; 
        inversion beval_a'; subst.
      rewrite H1; unfold isVI, project, vi, vi', inject'; simpl;
        rewrite out_in_fmap; repeat rewrite wf_functor; simpl; rewrite prj_inj.
      destruct (WF_invertVI _ WF_b d0_eq) as [beval_b' | beval_b']; 
        inversion beval_b'; subst.
      rewrite H3; unfold isVI, project, vi, vi', inject'; simpl;
        rewrite out_in_fmap; repeat rewrite wf_functor; simpl; rewrite prj_inj.
      apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
      simpl; rewrite wf_functor; simpl; eauto.
      unfold vi, vi', inject'; simpl; eauto;
        rewrite wf_functor; simpl; reflexivity.
      rewrite H0; unfold bot, isVI, project, inject, inject'; simpl;
        rewrite out_in_fmap; repeat rewrite wf_functor; simpl; unfold Bot_fmap.
      caseEq (prj (Sub_Functor := Sub_NatValue_V) (A:= (sig (@Universal_Property'_fold V _)))
        (inj (Bot (sig Universal_Property'_fold)))).
      elimtype False; eapply (inject_discriminate Dis_VI_Bot n0).
      unfold inject; simpl; apply inj_prj in H; erewrite <- H; reflexivity.
      caseEq (isBot V (in_t (inj (VI (Fix V) n)))).
      simpl in beval_b'.
      apply sym_eq in H0; apply sym_eq in d0_eq.
      generalize (WFV_proj1_a D V WFV _ _ WF_b _ _ H0).
      simpl; intros WF_b'; generalize (WFV_proj1_b D V WFV _ _ WF_b' _ _ d0_eq); simpl.
      assert (exist Universal_Property'_fold (bot V) (UP'_bot V) = bot' V) by 
        (unfold bot, UP'_bot; destruct bot'; reflexivity).
      assert (exist Universal_Property'_fold tnat UP'_tnat = tnat') by 
        (unfold tnat, UP'_tnat; destruct tnat'; reflexivity).
      unfold tnat, tnat', inject' at 1 in H5.
      unfold inject.
      rewrite H5, H4; auto.
      unfold isBot, project; simpl; rewrite out_in_fmap; 
        repeat rewrite wf_functor; simpl; unfold Bot_fmap; 
          rewrite prj_inj.
      simpl in beval_b'.
      apply sym_eq in H0; apply sym_eq in d0_eq.
      unfold eval in WF_b; generalize (WFV_proj1_a D V WFV _ _ WF_b _ _ H0).
      simpl; intros WF_b'; generalize (WFV_proj1_b D V WFV _ _ WF_b' _ _ d0_eq); simpl.
      assert (exist Universal_Property'_fold (bot V) (UP'_bot V) = bot' V) by 
        (unfold bot, UP'_bot; destruct bot'; reflexivity).
      assert (exist Universal_Property'_fold tnat UP'_tnat = tnat') by 
        (unfold tnat, UP'_tnat; destruct tnat'; reflexivity).
      unfold tnat, tnat', inject' at 1 in H5.
      unfold inject.
      rewrite H5, H4; auto.
      caseEq (isVI (proj1_sig (eval_rec a' gamma''))).
      unfold isVI in H; rewrite H0 in H.
      unfold bot, isVI, project, inject, inject' in H; simpl in H;
        rewrite out_in_fmap in H; repeat rewrite wf_functor in H; simpl in H;
          unfold Bot_fmap in H.
      caseEq (prj (Sub_Functor := Sub_NatValue_V) (A:= (sig (@Universal_Property'_fold V _)))
        (inj (Bot (sig Universal_Property'_fold)))).
      elimtype False; eapply (inject_discriminate Dis_VI_Bot n0);
        apply inj_prj in H1; unfold inject; rewrite <- H1; reflexivity.
      rewrite H1 in H; discriminate.
      rewrite H0.
      unfold bot, isBot, project, inject; simpl; rewrite out_in_fmap;
        repeat rewrite wf_functor; simpl; unfold Bot_fmap; simpl.
      simpl in beval_a'.
      apply sym_eq in H0; apply sym_eq in d_eq.
      generalize (WFV_proj1_a D V WFV _ _ WF_a _ _ H0).
      simpl; intros WF_a'; generalize (WFV_proj1_b D V WFV _ _ WF_a' _ _ d_eq); simpl.
      assert (exist Universal_Property'_fold (bot V) (UP'_bot V) = bot' V) by 
        (unfold bot, UP'_bot; destruct bot'; reflexivity).
      assert (exist Universal_Property'_fold tnat UP'_tnat = tnat') by 
        (unfold tnat, UP'_tnat; destruct tnat'; reflexivity).
      unfold tnat, tnat', inject' at 1 in H2.
      unfold inject.
      rewrite H2, H1, prj_inj; auto.
      exact (proj2_sig d0).
      exact (proj2_sig d0).
      exact (proj2_sig d).
      exact (proj2_sig d0).
    Defined.
         
    Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) F}.
    Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
      Sub_Arith_F (MAlgebra_typeof_Arith T) (Typeof_F _)}.
    Context {WF_Value_continous_alg : 
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

    Global Instance Arith_eval_Soundness_alg 
      (P_bind : Set)
      (P : P_bind -> Env Value -> Prop)
      (E' : Set -> Set)
      {Fun_E' : Functor E'}
      {Sub_Arith_E' : Arith :<: E'}
      {WF_Fun_E' : WF_Functor _ _ Sub_Arith_E' _ _}
      {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR _) E'}
      {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
        Sub_Arith_E' (MAlgebra_typeof_Arith T) (Typeof_E' _)}
      (pb : P_bind)
      (eval_rec : Exp -> evalR V)
      (typeof_rec : UP'_F E' -> typeofR D)
      :
      PAlgebra eval_Soundness_alg_Name (sig (UP'_P2 (@eval_alg_Soundness_P D _ V _ _ _ WFV _ P
        _ _ pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _ ))
        (f_algebra (FAlgebra := eval_F))))) Arith.
    Proof.
      econstructor; unfold Algebra; intros.
      eapply (ind2_alg_Arith (@eval_alg_Soundness_P D _ V _ F _ WFV _ P
        _ _ pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _))
        (f_algebra (FAlgebra := eval_F)))); try eassumption;
      unfold eval_alg_Soundness_P, UP'_P2; intros.
      constructor.
      exact (conj (proj2_sig (inject' (Lit _ n))) (proj2_sig (lit' n))).
      unfold lit, lit', inject; simpl.
      repeat rewrite out_in_fmap.
      repeat rewrite wf_functor.
      intros gamma'' WF_gamma'' IHa.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Arith_fmap.
      intros.
      eapply Arith_eval_Soundness_H.
      apply WF_eval_F.
      apply H0.
      (* Add Case *)
      destruct m as [m1 m2]; destruct n as [n1 n2];
        destruct IHm as [[UP'_m1 UP'_m2] IHm];
          destruct IHn as [[UP'_n1 UP'_n2] IHn]; simpl in *|-*.
      constructor.
      split; unfold inject; exact (proj2_sig _).
      unfold inject; simpl;
        repeat rewrite out_in_fmap; repeat rewrite wf_functor; simpl.
      intros eval_rec_proj typeof_rec_proj gamma'' WF_gamma'' IHa.
      rewrite (wf_algebra (WF_FAlgebra := WF_eval_F));
        rewrite (wf_algebra (WF_FAlgebra := WF_typeof_E' _));
          simpl fmap; simpl f_algebra; unfold Arith_fmap.
      intros T; eapply Arith_eval_Soundness_H0.
      apply WF_eval_F.
      apply (IHa _ _ WF_gamma'' (_, exist _ _ UP'_m2)); simpl;
        intros; apply (IHm eval_rec_proj typeof_rec_proj _ WF_gamma'' IHa);
          intros; auto; rewrite <- (in_out_UP'_inverse _ _ m1); auto.
      apply (IHa _ _ WF_gamma'' (_, exist _ _ UP'_n2)); simpl;
        intros; apply (IHn eval_rec_proj typeof_rec_proj _ WF_gamma'' IHa);
          intros; auto; rewrite <- (in_out_UP'_inverse _ _ n1); auto.
    Defined.

End Arith.

  Hint Extern 1 (iPAlgebra SV_invertVI_Name (SV_invertVI_P _) _) =>
      constructor; unfold iAlgebra; unfold SV_invertVI_P; intros i H n H0;
        inversion H; subst; simpl in H0; revert H0;
          match goal with H : proj1_sig ?v = _ |- proj1_sig ?v = _ -> _ => rewrite H end; intros;
            elimtype False; apply (inject_discriminate _ _ _ H0).

  Hint Extern 1 (iPAlgebra SV_invertVI'_Name (SV_invertVI'_P _) _) =>
      constructor; unfold iAlgebra; unfold SV_invertVI'_P; intros i H n H0;
        inversion H; subst; simpl in H0; revert H0;
          match goal with H : proj1_sig ?v = _ |- proj1_sig ?v = _ -> _ => rewrite H end; intros;
            elimtype False; apply (inject_discriminate _ _ _ H0).

  Hint Extern 5 (iPAlgebra WF_invertVI_Name (WF_invertVI_P _ _ _) _) =>
    constructor; unfold iAlgebra; intros i H; unfold WF_invertVI_P;
      inversion H; simpl;
      match goal with 
        eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ => 
          intro eq_H; rewrite eq_H in eq_H0;
            elimtype False; first [apply (inject_discriminate _ _ _ eq_H0) |
              apply sym_eq in eq_H0; apply (inject_discriminate _ _ _ eq_H0)]
      end : typeclass_instances.

Hint Extern 0 => 
  intros; match goal with 
            |- (PAlgebra eval_Soundness_alg_Name 
              (sig (UP'_P2 (eval_alg_Soundness_P _ _ _ _ _ _ _ _ _ _ _ _ _ _))) Arith) =>
            eapply Arith_eval_Soundness_alg; eauto with typeclass_instances
          end : typeclass_instances.


(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
