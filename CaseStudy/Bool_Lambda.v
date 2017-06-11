Require Import Coq.Program.Equality.
Require Import FJ_tactics.
Require Import List.
Require Import Polynomial.
Require Import Containers.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import Lambda.

Section PLambda_Bool.

  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {PFun_D : PFunctor D}.
  Context {SPF_D : SPF D}.
  Context {Sub_BType_D : BType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D}.
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D}.

  Variable E : Set -> Set -> Set.
  Context {Fun_E : forall A, Functor (E A)}.
  Context {PFun_E : forall A, PFunctor (E A)}.
  Context {SPF_E : forall A, SPF (E A)}.
  Context {Sub_Bool_E : forall A, Bool :<: (E A)}.
  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) (E (typeofR D))}.
  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {funEQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {PFun_V : PFunctor V}.
  Context {SPF_V : SPF V}.
  Context {Sub_BoolValue_V : BoolValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context {funWFV : iFunctor WFV}.
  Context {ispf_WFV : iSPF WFV}.

  Context {Sub_WFV_VB_WFV : Sub_iFunctor (WFValue_VB D V) WFV}.
  Context {Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV}.
  Context {Dis_Clos_Bot : Distinct_Sub_Functor LType BType D}.

  Context {Dis_VB_Clos : Distinct_Sub_Functor BoolValue (ClosValue E) V}.
  Context {WF_Sub_ClosValue_V : WF_Functor (ClosValue E) V Sub_ClosValue_V}.
  Context {WF_Sub_BoolValue_V : WF_Functor BoolValue V Sub_BoolValue_V}.

  Global Instance PAlgebra_WF_invertClos_VB typeof_rec :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    intros; discriminate_inject H0.
  Defined.

  Global Instance PAlgebra_WF_invertClos'_VB typeof_rec :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    intros; discriminate_inject H0.
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF BOOLEAN EXPRESSIONS             *)
  (* ============================================== *)

  Inductive Bool_eqv (A B : Set) (C : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
  | BLit_eqv : forall (gamma : Env _) gamma' b,
    Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' (blit (E A) b) (blit (E B) b))
  | If_eqv : forall (gamma : Env _) gamma' i t el i' t' el',
    C (mk_eqv_i _ _ _ gamma gamma' i i') ->
    C (mk_eqv_i _ _ _ gamma gamma' t t') ->
    C (mk_eqv_i _ _ _ gamma gamma' el el') ->
    Bool_eqv A B C (mk_eqv_i _ _ _ gamma gamma' (cond _ i t el) (cond _ i' t' el')).

  Lemma Bool_eqv_impl_NP_eqv : forall A B C i,
    Bool_eqv A B C i -> NP_Functor_eqv E Bool A B C i.
  Proof.
    intros; destruct H.
    unfold blit, blit in *; simpl in *.
    constructor 1 with (np := fun D => BLit D b); auto.
    simpl; intros; dependent destruction p; auto.
    constructor 4 with
      (a := i) (a' := i') (b := t) (b' := t') (c := el) (c' := el')
      (np := fun D => If D); auto.
    simpl; intros; dependent destruction p; auto.
    simpl; congruence.
  Defined.


End PLambda_Bool.
