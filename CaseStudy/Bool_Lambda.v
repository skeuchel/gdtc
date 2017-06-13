Require Import Coq.Program.Equality.
Require Import GDTC.
Require Import CaseStudy.Bool.
Require Import CaseStudy.Lambda.
Require Import CaseStudy.Names.
Require Import CaseStudy.PNames.

Section PLambda_Bool.

  Variable D : Set -> Set.
  Context `{spf_D : SPF D}.
  Context {Sub_BType_D : BType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_BType_D : WF_Functor _ _ Sub_BType_D}.
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D}.

  Variable E : Set -> Set -> Set.
  Context {fun_E : forall A, Functor (E A)}.
  Context {pfun_E: forall A, PFunctor (E A)}.
  Context {spf_E : forall A, SPF (E A)}.
  Context {Sub_Bool_E : forall A, Bool :<: (E A)}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Variable V : Set -> Set.
  Context `{spf_V : SPF V}.
  Context {Sub_BoolValue_V : BoolValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{spfWFV : iSPF _ WFV}.

  Context {Dis_VB_Clos : Distinct_Sub_Functor BoolValue (ClosValue E) V}.
  Context {WF_Sub_ClosValue_V : WF_Functor (ClosValue E) V Sub_ClosValue_V}.
  Context {WF_Sub_BoolValue_V : WF_Functor BoolValue V Sub_BoolValue_V}.

  Context {Sub_WFV_VB_WFV : Sub_iFunctor (WFValue_VB D V) WFV}.
  Context {Dis_LType_BType : Distinct_Sub_Functor LType BType D}.

  Global Instance PAlgebra_WF_invertClos_VB typeof_rec :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    constructor; unfold iAlgebra, WF_invertClos_P.
    inversion 1; subst; simpl; split.
    - apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    - intros ? ? Heq; discriminate_inject Heq.
  Qed.

  Global Instance PAlgebra_WF_invertClos'_VB typeof_rec :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P D E V EQV_E WFV typeof_rec) (WFValue_VB D V).
  Proof.
    constructor; unfold iAlgebra, WF_invertClos_P.
    inversion 1; subst; simpl; split.
    - apply (inject_i (subGF := Sub_WFV_VB_WFV)); econstructor; eauto.
    - intros ? Heq; discriminate_inject Heq.
  Qed.

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

  Lemma Bool_eqv_impl_NP_eqv A B C i :
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
  Qed.

End PLambda_Bool.
