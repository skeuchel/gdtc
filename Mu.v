Require Import FJ_tactics.
Require Import List.
Require Import Polynomial.
Require Import Containers.
Require Import Functors.
Require Import Names.
Require Import PNames.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Section Mu.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Fixpoint Expressions *)
  Variable D : Set -> Set.
  Context {Fun_D : Functor D}.
  Context {PFun_D : PFunctor D}.
  Context {SPF_D : SPF D}.

  Inductive Fix_ (A E : Set) : Set :=
  | Mu : DType D -> (A -> E) -> Fix_ A E.

  (** Container Instance **)

  Global Instance Fix_Iso (A : Set) :
    Iso (Fix_ A) (K (DType D) :*: Fn A) :=
    {| fromIso := fun E e => match e with
                               | Mu d f       => (d,f)
                             end;
       toIso   := fun E e => match e with
                               | (d,f) => Mu _ _ d f
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [d f]; reflexivity.
  Defined.

  Global Instance Fix_Container (A : Set) : Container (Fix_ A) :=
    ContainerIso (Fix_Iso A).

  Variable F : Set -> Set -> Set.
  Context {Sub_Fix_F : forall A : Set, Fix_ A :<: F A}.
  Context {Fun_F : forall A, Functor (F A)}.
  Context {PFun_F: forall A, PFunctor (F A)}.
  Context {SPF_F : forall A, SPF (F A)}.

  Definition Exp (A : Set) := Exp (F A).

  (* Constructors + Universal Property. *)

  Context {WF_Sub_Fix_F : forall A, WF_Functor _ _ (Sub_Fix_F A)}.

  Definition mu {A : Set}
    (t1 : DType D) (f : A -> Exp A) :
    Exp A := inject (Mu _ _ t1 f).

  (* Induction Principle for PLambda. *)
  Definition ind_alg_Fix {A : Set}
    (P : Exp A -> Prop)
    (Hmu : forall d f, (forall a, P (f a)) -> P (mu d f))
      : PAlgebra (inject' (Fix_ A)) P :=
    fun xs =>
      match xs return All P xs -> P (inject' (Fix_ A) xs) with
        | Mu d f =>
          fun Axs : forall p : _ + _, _ => Hmu d f (fun a => Axs (inr a))
      end.

  (* Typing for Lambda Expressions. *)

  Context {Eq_DType : Eq (DType D)}.

  Definition Fix_typeof (R : Set) (rec : R -> typeofR D) (e : Fix_ (typeofR D) R) : typeofR D:=
  match e with
    | Mu t1 f => match rec (f (Some t1)) with
                     | Some t2 => if (eq_DType D t1 t2) then
                       Some t1 else None
                     | _ => None
                   end
  end.

  Global Instance MAlgebra_typeof_Fix T:
    FAlgebra TypeofName T (typeofR D) (Fix_ (typeofR D)) :=
    {| f_algebra := Fix_typeof T|}.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {PFun_V: PFunctor V}.
  Context {SPF_V : SPF V}.

  Definition Value := Value V.

  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V}.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)

  Definition Fix_eval : Mixin (Exp nat) (Fix_ nat) (evalR V) :=
    fun rec e =>
     match e with
       | Mu t1 f => fun env =>
         rec (f (length env)) (insert _ (rec (mu t1 f) env) env)
     end.

(* Evaluation Algebra for Lambda Expressions. *)

  Global Instance MAlgebra_eval_Fix :
    FAlgebra EvalName (Exp nat) (evalR V) (Fix_ nat) :=
    {| f_algebra := Fix_eval|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import String.
  Require Import Ascii.

  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR D}.

  Definition PLambda_ExpPrint (R : Set) (rec : R -> ExpPrintR)
    (e : Fix_ nat R) : ExpPrintR :=
    match e with
      | Mu t1 f => fun n => append "|\/| x" ((String (ascii_of_nat n) EmptyString) ++
        " : " ++ (DTypePrint _ t1) ++ ". " ++
        (rec (f n) (S n)) ++ ")")
    end.

  Global Instance MAlgebra_Print_Fix T :
    FAlgebra ExpPrintName T ExpPrintR (Fix_ nat) :=
    {| f_algebra := PLambda_ExpPrint T|}.

  Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR (F nat)}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Fix_ nat) (F nat)
    (Sub_Fix_F nat) (MAlgebra_eval_Fix) (eval_F)}.

  (* Continuity of Evaluation. *)
  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context `{ispf_SV : iSPF _ SV}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

  (* Mu case. *)

  Lemma eval_continuous_Exp_H : forall t1 f
    (IHf : forall a, eval_continuous_Exp_P V (F nat) SV (f a)),
    eval_continuous_Exp_P V (F nat) SV (mu t1 f).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    unfold mu, inject; simpl_beval.
    rewrite (P2_Env_length _ _ _ _ _ H0).
    apply H; auto.
    apply P2_Env_insert; auto.
  Qed.

  Global Instance Fix_eval_continuous_Exp :
    FPAlgebra (eval_continuous_Exp_P V (F nat) SV) (inject' (Fix_ nat)).
  Proof.
    constructor; unfold PAlgebra; intros.
    apply ind_alg_Fix.
    apply eval_continuous_Exp_H.
    assumption.
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF EXPRESSIONS                     *)
  (* ============================================== *)

  Inductive Fix_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
  | Mu_eqv : forall (gamma : Env _) gamma' f g d,
    (forall (a : A) (b : B),
      E (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))) ->
    Fix_eqv _ _ E (mk_eqv_i _  _ _ gamma gamma' (mu d f) (mu d g)).

  Inductive Fix_eqv_S (A B : Set) : eqv_i F A B -> Set :=
  | SMu_eqv : forall (gamma : Env _) gamma' f g d,
    Fix_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (mu d f) (mu d g)).

  Definition Fix_eqv_P (A B : Set) (i : eqv_i F A B) (s : Fix_eqv_S A B i) : Set.
    destruct s.
    apply ((A * B)%type).
  Defined.

  Definition Fix_eqv_R (A B : Set) (i : eqv_i F A B)
             (s : Fix_eqv_S A B i)
             (p : Fix_eqv_P A B i s) : eqv_i F A B.
  Proof.
    destruct s; simpl in p.
    destruct p.
    apply (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b)).
  Defined.

  Definition Fix_eqv_to (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    IExt _ _ (Fix_eqv_R A B) C i -> Fix_eqv A B C i.
  Proof.
    intros x; destruct x; destruct s; simpl in pf.
    constructor; intros.
    apply (pf (a , b)).
  Defined.

  Definition Fix_eqv_from (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    Fix_eqv A B C i -> IExt _ _ (Fix_eqv_R A B) C i.
  Proof.
    intros x; destruct x.
    constructor 1 with (s := SMu_eqv _ _ gamma gamma' f g d); simpl.
    intro p; destruct p; auto.
  Defined.

  Global Instance Fix_eqv_Container (A B : Set) : IContainer (Fix_eqv A B) :=
    {| IS    := Fix_eqv_S A B;
       IP    := Fix_eqv_P A B;
       IR    := Fix_eqv_R A B;
       ifrom := Fix_eqv_from A B;
       ito   := Fix_eqv_to A B
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl; f_equal;
      extensionality x; destruct x; try destruct u; reflexivity.
  Defined.

  Definition ind_alg_Fix_eqv
    (A B : Set)
    (P : eqv_i F A B -> Prop)
    (Hmu : forall gamma gamma' f g d
      (IHf : forall a b, P (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))),
      P (mk_eqv_i _ _ _ gamma gamma' (mu d f) (mu d g)))
    i (e : Fix_eqv A B P i) : P i :=
    match e in Fix_eqv _ _ _ i return P i with
      | Mu_eqv gamma gamma' f g d eqv_f_g  =>
        Hmu gamma gamma' f g d eqv_f_g
    end.

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Context {fun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Variable Sub_Fix_eqv_EQV_E : forall A B,
    Sub_iFunctor (Fix_eqv A B) (EQV_E A B).

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) (F (typeofR D))}.

  (* ============================================== *)
  (* WELL-FORMED FUNCTION VALUES                    *)
  (* ============================================== *)

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{ispf_WFV : iSPF _ WFV}.
  Context {Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV}.

  Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T _ _ _
    (Sub_Fix_F _) (MAlgebra_typeof_Fix T) (Typeof_F _)}.
  Context {WF_Value_continous_alg :
    iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

  Variable typeof_rec : Exp (typeofR D) -> typeofR D.

  Context {eval_continuous_Exp_E :
    FPAlgebra (eval_continuous_Exp_P V (F nat) SV) (inject' (F nat))}.

  Global Instance Fix_Soundness : forall eval_rec,
    iPAlgebra soundness_XName
    (soundness_X'_P D V F EQV_E WFV
      (typeof _ _) eval_rec
      (f_algebra (FAlgebra := Typeof_F _))
      (f_algebra (FAlgebra := eval_F))) (Fix_eqv _ _).
  Proof.
    constructor; unfold iAlgebra; intros.
    apply ind_alg_Fix_eqv; try eassumption;
    unfold soundness_X'_P; simpl; intros.
    (* mu case *)
    split; intros.
    apply (inject_i (subGF := Sub_Fix_eqv_EQV_E _ _)); constructor; auto.
    intros; destruct (IHf a b) as [f_eqv _]; auto.
    unfold eval_alg_Soundness_P.
    unfold Fix' in *.
    unfold beval, mu, inject; simpl; repeat rewrite wf_functor; simpl.
    repeat rewrite out_in_inverse.
    rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl; intros.
    rename H0 into typeof_e.
    unfold mu, inject in typeof_e.
    rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)) in typeof_e;
      simpl in typeof_e.
    caseEq (typeof _ _ (f (Some d))); unfold typeofR, DType, Names.DType in *|-*;
      rename H0 into typeof_f; rewrite typeof_f in typeof_e; try discriminate.
    caseEq (eq_DType _ d d0); rename H0 into eq_d_d0;
      rewrite eq_d_d0 in typeof_e; try discriminate.
    injection typeof_e; intros; subst; clear typeof_e.
    generalize (eq_DType_eq D _ _ eq_d_d0); intro; subst.
    intros; destruct (IHf (Some d0) (Datatypes.length gamma'')) as [g_eqv _]; auto.
    apply IH with
      (e := f (Some d0))
      (pb := (insert (option _) (Some d0) gamma,
        insert nat (Datatypes.length gamma'') gamma')); auto.
    assert (Datatypes.length gamma'' = Datatypes.length gamma') by
      (destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]];
        simpl in *|-*; rewrite <- WF_gamma2; eapply P2_Env_length; eauto).
    rewrite H0.
    apply WF_eqv_environment_P_insert; auto.
    generalize (fun a b => proj1 (IHf a b IH)) as f_eqv; intros.
    apply IH with (e := mu d0 f) (1 := WF_gamma'').
    apply (inject_i (subGF := Sub_Fix_eqv_EQV_E _ _)).
    constructor; auto.
    revert typeof_f; unfold typeof, in_t.
    unfold mu, inject.
    rewrite fold_computation, wf_functor, (wf_mixin (WF_Mixin := WF_typeof_F _));
      simpl; unfold id at 2; fold (typeof D _); intros.
    unfold DType, Fix', typeofR in *.
    rewrite typeof_f, eq_d_d0; reflexivity.
  Defined.
End Mu.
