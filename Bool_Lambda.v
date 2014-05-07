Require Import FJ_tactics.
Require Import List.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Lambda.

Section PLambda_Arith.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Definition DType := DType D.
  Context {Sub_BType_D : BType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D _ _}.
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D _ _}.
  Context {eq_DType_D : forall T, FAlgebra eq_DTypeName T (eq_DTypeR D) D}.
  Context {eq_TArrow_D : forall T, FAlgebra eq_TArrowName T (eq_TArrowR D) D}.

  Definition BType_eq_TArrow (R : Set) (rec : R -> eq_TArrowR D) 
    (e : BType R) : eq_TArrowR D := (fun _ _ => false, tbool' D).

  Global Instance MAlgebra_eq_TArrow_BType T:
    FAlgebra eq_TArrowName T (eq_TArrowR D) BType | 4 :=
      {| f_algebra := BType_eq_TArrow T|}.

  Context {WF_TArrow_eq_DT : forall T, @WF_FAlgebra eq_TArrowName T _ _ _
    Sub_BType_D (MAlgebra_eq_TArrow_BType T) (eq_TArrow_D _)}. 

  Global Instance PAlgebra_eq_TArrow_eq_BType :
    PAlgebra eq_TArrow_eqName (sig (UP'_P (eq_TArrow_eq_P D))) BType.
  Proof.
    constructor; unfold Algebra; intros.
    eapply ind_alg_BType.
    unfold UP'_P; econstructor.
    unfold eq_TArrow_eq_P; intros.
    unfold eq_DType, mfold, tbool, tbool', inject' in H; simpl in H;
      repeat rewrite wf_functor in H; simpl in H; unfold in_t in H. 
    simpl.
    unfold eq_TArrow, mfold, tbool; simpl; rewrite wf_functor; simpl;
      unfold in_t at 1; simpl; unfold BType_fmap.
    rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)); simpl.
    rewrite wf_functor; simpl; unfold BType_fmap; split; auto.
    simpl; intros.
    unfold in_t in H0; rewrite (wf_algebra (WF_FAlgebra := WF_TArrow_eq_DT _)) in H0; 
      simpl in H0; discriminate.
    exact H.
  Defined.

  Global Instance WF_BType_eq_TArrow_eq 
    {Sub_BType_D' : BType :<: D} :
    (forall a, inj (Sub_Functor := Sub_BType_D) a =
      inj (A := Fix D) (Sub_Functor := Sub_BType_D') a) -> 
    WF_Ind (sub_F_E := Sub_BType_D') PAlgebra_eq_TArrow_eq_BType.
  Proof.
    constructor; destruct e; simpl; intros.
    unfold tbool, tbool'; simpl; rewrite wf_functor; simpl;
      unfold BType_fmap; auto.
    rewrite H; reflexivity.
  Defined.

  Variable E : Set -> Set -> Set.
  Context {Fun_E : forall A, Functor (E A)}.
  Context {Sub_Bool_E : forall A, Bool :<: (E A)}.
  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR _) (E (typeofR _))}.
  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {Sub_BoolValue_V : BoolValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context {funWFV : iFunctor WFV}.

  Context {Sub_WFV_VB_WFV : Sub_iFunctor (WFValue_VB D V) WFV}.
  Context {Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV}.
  Context {Dis_Clos_Bot : Distinct_Sub_Functor _ Sub_LType_D Sub_BType_D}.

  Context {Dis_VB_Clos : Distinct_Sub_Functor Fun_V Sub_BoolValue_V Sub_ClosValue_V}.
  Context {WF_Sub_ClosValue_V : WF_Functor (ClosValue E) V Sub_ClosValue_V _ Fun_V}.
  Context {WF_Sub_BoolValue_V : WF_Functor BoolValue V Sub_BoolValue_V _ Fun_V}.

  Global Instance PAlgebra_WF_invertClos_VB typeof_rec : 
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    intros; rewrite H2 in H1.
    elimtype False; apply (inject_discriminate _ _ _ H1).    
  Defined.

  Global Instance PAlgebra_WF_invertClos'_VB typeof_rec : 
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    simpl in *|-*; intros; rewrite H2 in H0.
    elimtype False; apply sym_eq in H0. apply (inject_discriminate _ _ _ H0).    
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF BOOLEAN EXPRESSIONS             *)
  (* ============================================== *)

    Inductive Bool_eqv (A B : Set) (C : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
    | BLit_eqv : forall (gamma : Env _) gamma' n e e', 
      proj1_sig e = blit (E A) n -> 
      proj1_sig e' = blit (E B) n -> 
      Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e')
    | If_eqv : forall (gamma : Env _) gamma' i t el i' t' el' e e',
      C (mk_eqv_i _ _ _ gamma gamma' i i') -> 
      C (mk_eqv_i _ _ _ gamma gamma' t t') -> 
      C (mk_eqv_i _ _ _ gamma gamma' el el') -> 
      proj1_sig e = proj1_sig (cond' _ i t el) ->  
      proj1_sig e' = proj1_sig (cond' _ i' t' el') -> 
      Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' e e'). 
    
    Lemma Bool_eqv_impl_NP_eqv : forall A B C i, 
      Bool_eqv A B C i -> NP_Functor_eqv E Bool A B C i.
      intros; destruct H.
      unfold blit, blit in *; simpl in *.
      constructor 1 with (np := fun D => BLit D n); auto.
      econstructor 4 with (np := fun D => If D); eauto.
      simpl; congruence.
    Defined.


End PLambda_Arith.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*) 
