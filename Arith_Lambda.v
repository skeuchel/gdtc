Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Lambda.
Require Import PNames.

Section Lambda_Arith.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_AType_D : AType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_AType_D : WF_Functor _ _ Sub_AType_D _ _}.
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D _ _}.
  Context {eq_DType_D : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_TArrow_D : forall T, FAlgebra eq_TArrowName T (eq_TArrowR D) D}.

  Definition AType_eq_TArrow (R : Set) (rec : R -> eq_TArrowR D) 
    (e : AType R) : eq_TArrowR D := (fun _ _ => false, tnat' D).

  Global Instance MAlgebra_eq_TArrow_AType T:
    FAlgebra eq_TArrowName T (eq_TArrowR D) AType | 4 :=
      {| f_algebra := AType_eq_TArrow T|}.

  Context {WF_TArrow_eq_DT : forall T, @WF_FAlgebra eq_TArrowName T _ _ _
    Sub_AType_D (MAlgebra_eq_TArrow_AType T) (eq_TArrow_D _)}. 

  Global Instance PAlgebra_eq_TArrow_eq_AType :
    PAlgebra eq_TArrow_eqName (sig (UP'_P (eq_TArrow_eq_P D))) AType.
  Proof.
    constructor; unfold Algebra; intros.
    eapply ind_alg_AType.
    unfold UP'_P; econstructor.
    unfold eq_TArrow_eq_P; intros.
    unfold eq_DType, mfold, tnat, tnat', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H. 
    simpl.
    unfold eq_TArrow, mfold, tnat; simpl; rewrite wf_functor; simpl;
      unfold in_t at 1; simpl; unfold AType_fmap.
    rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)); simpl.
    rewrite wf_functor; simpl; unfold AType_fmap; split; auto.
    simpl; intros.
    unfold in_t in H0; rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)) in H0; 
      simpl in H0; discriminate.
    exact H.
  Defined.

  Variable E : Set -> Set -> Set.
  Context {Fun_E : forall A, Functor (E A)}.
  Context {Sub_Arith_E : forall A, Arith :<: (E A)}.
  Context {WF_Sub_Arith_E : forall A, WF_Functor _ _ (Sub_Arith_E A) _ _}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_NatValue_V : NatValue :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context {funWFV : iFunctor WFV}.

  Context {Dis_VI_Clos : Distinct_Sub_Functor Fun_V Sub_NatValue_V Sub_ClosValue_V}.
  Context {WF_Sub_ClosValue_V : WF_Functor (ClosValue E) V Sub_ClosValue_V _ Fun_V}.
  Context {WF_Sub_NatValue_V : WF_Functor NatValue V Sub_NatValue_V _ Fun_V}.

  Context {Sub_WFV_VI_WFV : Sub_iFunctor (WFValue_VI D V) WFV}.
  Context {Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV}.
  Context {Dis_Clos_Bot : Distinct_Sub_Functor _ Sub_LType_D Sub_AType_D}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR _) (E (typeofR _))}.
  Context {WF_typeof_E : forall T, @WF_FAlgebra TypeofName T _ _ _
    (Sub_Arith_E _) (MAlgebra_typeof_Arith _ T) (Typeof_E _)}.

  Global Instance PAlgebra_WF_invertClos_VI typeof_rec : 
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E V EQV_E WFV typeof_rec) (WFValue_VI D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
    intros; rewrite H2 in H1.
    elimtype False; apply (inject_discriminate _ _ _ H1).    
  Defined.

  Global Instance PAlgebra_WF_invertClos'_VI typeof_rec : 
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P D E V EQV_E WFV typeof_rec) (WFValue_VI D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
    simpl in *|-*; intros; rewrite H2 in H0.
    elimtype False; apply sym_eq in H0. apply (inject_discriminate _ _ _ H0).    
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF ARITHMETIC EXPRESSIONS          *)
  (* ============================================== *)

    Inductive Arith_eqv (A B : Set) (C : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
    | Lit_eqv : forall (gamma : Env _) gamma' n e e', 
      proj1_sig e = lit (E A) n -> 
      proj1_sig e' = lit (E B) n -> 
      Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
    | Add_eqv : forall (gamma : Env _) gamma' a b a' b' e e',
      C (mk_eqv_i _ _ _ gamma gamma' a a') -> 
      C (mk_eqv_i _ _ _ gamma gamma' b b') -> 
      proj1_sig e = proj1_sig (add' (E _) a b) ->  
      proj1_sig e' = proj1_sig (add' (E _) a' b') -> 
      Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e'). 

    Lemma Arith_eqv_impl_NP_eqv : forall A B C i, 
      Arith_eqv A B C i -> NP_Functor_eqv E  Arith A B C i.
      intros; destruct H.
      unfold lit in *; simpl in *.
      constructor 1 with (np := fun D => Lit D n); auto.
      econstructor 3 with (np := fun D => Add D); eauto.
      simpl; congruence.
    Defined.


End Lambda_Arith.


(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
