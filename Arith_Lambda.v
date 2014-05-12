Require Import Coq.Program.Equality.
Require Import FJ_tactics.
Require Import List.
Require Import Polynomial.
Require Import Containers.
Require Import Functors.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Lambda.
Require Import PNames.

Section Lambda_Arith.

  Variable D : Set -> Set.
  Context `{spf_D : SPF D}.
  Context {Sub_AType_D : AType :<: D}.
  Context {Sub_LType_D : LType :<: D}.
  Context {WF_Sub_AType_D : WF_Functor _ _ Sub_AType_D}.
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D}.

  Variable E : Set -> Set -> Set.
  Context {fun_E : forall A, Functor (E A)}.
  Context {pfun_E: forall A, PFunctor (E A)}.
  Context {spf_E : forall A, SPF (E A)}.
  Context {Sub_Arith_E : forall A, Arith :<: (E A)}.
  Context {WF_Sub_Arith_E : forall A, WF_Functor _ _ (Sub_Arith_E A)}.

  Variable EQV_E : forall A B, (eqv_i E A B -> Prop) -> eqv_i E A B -> Prop.
  Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Variable V : Set -> Set.
  Context `{spf_V : SPF V}.
  Context {Sub_NatValue_V : NatValue :<: V}.
  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {Sub_ClosValue_V : ClosValue E :<: V}.
  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{spfWFV : iSPF _ WFV}.

  Context {Dis_VI_Clos : Distinct_Sub_Functor NatValue (ClosValue E) V}.
  Context {WF_Sub_ClosValue_V : WF_Functor (ClosValue E) V Sub_ClosValue_V}.
  Context {WF_Sub_NatValue_V : WF_Functor NatValue V Sub_NatValue_V}.

  Context {Sub_WFV_VI_WFV : Sub_iFunctor (WFValue_VI D V) WFV}.
  Context {Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV}.
  Context {Dis_LType_AType : Distinct_Sub_Functor LType AType D}.

  Context {Typeof_E : forall T, FAlgebra TypeofName T (typeofR D) (E (typeofR _))}.
  Context {WF_typeof_E : forall T, WF_FAlgebra TypeofName T _ _ _
    (MAlgebra_typeof_Arith _ T) (Typeof_E _)}.

  Global Instance PAlgebra_WF_invertClos_VI typeof_rec :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P D E V EQV_E WFV typeof_rec) (WFValue_VI D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
    intros; discriminate_inject H0.
  Defined.

  Global Instance PAlgebra_WF_invertClos'_VI typeof_rec :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P D E V EQV_E WFV typeof_rec) (WFValue_VI D V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); econstructor; eauto.
    intros; discriminate_inject H0.
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF ARITHMETIC EXPRESSIONS          *)
  (* ============================================== *)

  Inductive Arith_eqv (A B : Set) (C : eqv_i E A B -> Prop) : eqv_i E A B -> Prop :=
  | Lit_eqv : forall (gamma : Env _) gamma' n,
    Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' (lit (E A) n) (lit (E B) n))
  | Add_eqv : forall (gamma : Env _) gamma' a b a' b',
    C (mk_eqv_i _ _ _ gamma gamma' a a') ->
    C (mk_eqv_i _ _ _ gamma gamma' b b') ->
    Arith_eqv A B C (mk_eqv_i _ _ _ gamma gamma' (add (E _) a b) (add (E _) a' b')).

  Lemma Arith_eqv_impl_NP_eqv : forall A B C i,
    Arith_eqv A B C i -> NP_Functor_eqv E  Arith A B C i.
  Proof.
    intros; destruct H.
    unfold lit in *; simpl in *.
    constructor 1 with (np := fun D => Lit D n); auto.
    simpl; intros; dependent destruction p; auto.
    constructor 3 with (a := a) (a' := a') (b := b) (b' := b') (np := Add); auto.
    simpl; intros; dependent destruction p; auto.
    simpl; congruence.
  Defined.

End Lambda_Arith.
