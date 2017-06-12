Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Equality.
Require Import List.
Require Import GDTC.FJ_tactics.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.
Require Import CaseStudy.Names.
Require Import CaseStudy.PNames.

Section Lambda.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* Function Types. *)
  Inductive LType (A : Set) : Set :=
    TArrow : A -> A -> LType A.

  Definition ltype_pto (A : Set) : ExtP A (I * I) -> LType A.
    intro x.
    inversion x; subst.
    inversion H1.
    inversion H2.
    constructor.
    apply H.
    apply H0.
  Defined.

  Definition ltype_pfrom (A : Set) : LType A -> ExtP A (I * I) :=
    fun x => match x with
               | TArrow y z => ep _ (ei _ y) (ei _ z)
             end.

  Global Instance LType_Polynomial : Polynomial LType :=
    {| PCode := (I * I)%poly;
       pto   := ltype_pto;
       pfrom := ltype_pfrom
    |}.
  Proof.
    intros A a;
      dependent destruction a;
      reflexivity.
    intros A a;
      dependent destruction a;
      dependent destruction a1;
      dependent destruction a2.
    reflexivity.
  Defined.

  Global Instance LType_Container : Container LType | 6 :=
    PolynomialContainer LType.

  Variable D : Set -> Set.
  Context {Sub_LType_D  : LType :<: D}.
  Context `{spf_D : SPF D}.
  Definition DType := DType D.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_LType_D : WF_Functor _ _ Sub_LType_D}.

  Definition tarrow (t1 t2 : DType) := inject LType D (TArrow _ t1 t2).

  (* Algebra for testing type equality. *)

  Definition isTArrow : DType -> option (_ * _) :=
    fun typ =>
      match project LType D typ with
       | Some (TArrow t1 t2)  => Some (t1, t2)
       | None                 => None
      end.

  Context {Eq_DType : Eq DType}.

  (* End type equality section. *)


  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (* Lambda Expressions *)
  Inductive Lambda (A E : Set) : Set :=
  | Var : A -> Lambda A E
  | App : E -> E -> Lambda A E
  | Lam : DType -> (A -> E) -> Lambda A E.

  (** Container Instance **)

  Global Instance Lambda_Iso (A : Set) :
    Iso (Lambda A) (K A :+: Id :*: Id :+: K DType :*: Fn A) :=
    {| fromIso := fun E e => match e with
                               | Var a     => inl a
                               | App e1 e2 => inr (inl (e1,e2))
                               | Lam d f   => inr (inr (d,f))
                             end;
       toIso   := fun E e => match e with
                               | inl a             => Var _ _ a
                               | inr (inl (e1,e2)) => App _ _ e1 e2
                               | inr (inr (d,f))   => Lam _ _ d f
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [n|[[e1 e2]|[d f]]]; reflexivity.
  Defined.

  Global Instance Lambda_Container (A : Set) : Container (Lambda A) :=
    ContainerIso (Lambda_Iso A).

  (* Inductive LambdaS (A : Set) := *)
  (* | SVar : A -> LambdaS A *)
  (* | SApp : LambdaS A *)
  (* | SLam : DType -> LambdaS A. *)

  (* Inductive LambdaP (A : Set) : LambdaS A -> Set := *)
  (* | PApp1 : LambdaP A (SApp A) *)
  (* | PApp2 : LambdaP A (SApp A) *)
  (* | PLam  : forall d, A -> LambdaP A (SLam _ d). *)

  (* Global Implicit Arguments PApp1 [[A]]. *)
  (* Global Implicit Arguments PApp2 [[A]]. *)
  (* Global Implicit Arguments PLam [[A]]. *)

  (* Definition fromLambda (A E : Set) (x : Lambda A E) : Ext (LambdaS A) (LambdaP A) E. *)
  (*   destruct x. *)
  (*   apply ext with (s := SVar _ a). *)
  (*   intro p. *)
  (*   inversion p. *)
  (*   apply ext with (s := SApp _). *)
  (*   intro p. *)
  (*   inversion p. *)
  (*   apply e. *)
  (*   apply e0. *)
  (*   apply ext with (s := SLam _ d). *)
  (*   intro p. *)
  (*   inversion p. *)
  (*   apply (e H0). *)
  (* Defined. *)

  (* Definition toLambda (A E : Set) (x : Ext (LambdaS A) (LambdaP A) E) : Lambda A E := *)
  (*   match x with *)
  (*     | ext s pf => *)
  (*       match s as s return ((LambdaP A s -> E) -> Lambda A E) with *)
  (*         | SVar a => fun pf => Var A E a *)
  (*         | SApp   => fun pf => App A E (pf PApp1) (pf PApp2) *)
  (*         | SLam d => fun pf => Lam A E d (fun p => pf (PLam d p)) *)
  (*       end pf *)
  (*   end. *)

  (* Global Instance Lambda_Container (A : Set) : Container (Lambda A) := *)
  (*   {| Shape    := LambdaS A; *)
  (*      Position := LambdaP A; *)
  (*      from     := fromLambda A; *)
  (*      to       := toLambda A |}. *)
  (* Proof. *)
  (*   intros E x. *)
  (*   destruct x; reflexivity. *)
  (*   intros E x. *)
  (*   destruct x as [[] pf]; *)
  (*     simpl; *)
  (*     f_equal; *)
  (*     extensionality p; *)
  (*     dependent destruction p; *)
  (*     reflexivity. *)
  (* Defined. *)

  Variable F : Set -> Set -> Set.
  Context {Sub_Lambda_F : forall A : Set, Lambda A :<: F A}.
  Context {fun_F : forall A, Functor (F A)}.
  Context {pfun_F: forall A, PFunctor (F A)}.
  Context {spf_F : forall A, SPF (F A)}.
  Definition Exp (A : Set) := Exp (F A).

  (* Constructors + Universal Property. *)

  Context {WF_Sub_Lambda_F : forall A, WF_Functor _ _ (Sub_Lambda_F A)}.

  Definition var {A : Set} (a : A) : Exp A := inject (Lambda A) (F A) (Var _ _ a).
  Definition app {A : Set} (e1 e2 : Exp A) := inject (Lambda A) (F A) (App _ _ e1 e2).
  Definition lam {A : Set} (t1 : DType) (f : A -> Exp A) := inject (Lambda A) (F A) (Lam _ _ t1 f).

  (* Induction Principle for Lambda. *)
  Definition ind_alg_Lambda {A : Set}
    (P : Fix (F A) -> Prop)
    (Hvar : forall x, P (var x))
    (Happ : forall e1 e2, P e1 -> P e2 -> P (app e1 e2))
    (Hlam : forall t1 f, (forall a, P (f a)) -> P (lam t1 f))
      : PAlgebra (inject (Lambda A) (F A)) P :=
    fun xs =>
      match xs return All P xs -> P (inject (Lambda A) (F A) xs) with
        | Var a     => fun _ => Hvar a
        | App e1 e2 =>
          fun Axs : forall p : _ + _, _ =>
            Happ e1 e2 (Axs (inl tt)) (Axs (inr tt))
        | Lam d f =>
          fun Axs : forall p : _ + _, _ =>
            Hlam d f (fun a => Axs (inr a))
      end.

  (* Typing for Lambda Expressions. *)

  Definition Lambda_typeof (R : Set) (rec : R -> typeofR D) (e : Lambda (typeofR D) R) : typeofR D:=
  match e with
    | Var v => v
    | App e1 e2 =>
      match (rec e1, rec e2) with
        | (Some t1, Some t3) =>
          match (isTArrow t1) with
            | Some (t1, t2) =>
              if (eq_DType D t1 t3) then Some t2 else None
            | _ => None
          end
        | _ => None
      end
    | Lam t1 f =>
      match rec (f (Some t1)) with
        | Some t2 => Some (inject LType D (TArrow _ t1 t2))
        | _ => None
      end
  end.

  Global Instance MAlgebra_typeof_Lambda T:
    FAlgebra TypeofName T (typeofR D) (Lambda (typeofR D)) :=
    {| f_algebra := Lambda_typeof T|}.

  (* Function Values. *)

  Inductive ClosValue (A : Set) : Set :=
  | Clos : Exp nat -> Env A -> ClosValue A.

  Global Instance ClosValue_Iso : Iso ClosValue (K (Exp nat) :*: list) :=
    {| fromIso := fun A x => match x with
                               | Clos e env => (e , env)
                             end;
       toIso   := fun A x => match x with
                               | (e , env) => Clos _ e env
                             end
    |}.
  Proof.
    destruct a; auto.
    destruct a; auto.
  Qed.

  Global Instance ContainerClos : Container ClosValue :=
    ContainerIso ClosValue_Iso.

  Variable V : Set -> Set.
  Context `{spf_V : SPF V}.
  Context {Sub_ClosValue_V : ClosValue :<: V}.
  Definition Value := Value V.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_ClosValue_V : WF_Functor _ _ (Sub_ClosValue_V)}.

  Definition closure f env : Value := inject ClosValue V (Clos _ f env).

  (* Constructor Testing for Function Values. *)

  Definition isClos : Fix V -> option _ :=
    fun exp =>
     match project ClosValue V exp with
      | Some (Clos f env)  => Some (f, env)
      | None             => None
     end.

  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {Sub_BotValue_V : BotValue :<: V}.

  Definition Lambda_eval : Mixin (Exp nat) (Lambda nat) (evalR V) :=
    fun rec e =>
      match e with
        | Var v =>
          fun env =>
            match lookup env v with
              | Some y => y
              | None => stuck _ 20
            end
        | App e1 e2 =>
          fun env =>
            let reced := (rec e1 env) in
            match isClos reced with
              | Some (f, env') => rec f (insert _ (rec e2 env) env')
              | None => if isBot _ reced then bot _ else stuck _ 5
            end
        | Lam t1 f => fun env => closure (f (length env)) env
      end.

  Global Instance MAlgebra_eval_Lambda :
    FAlgebra EvalName (Exp nat) (evalR V) (Lambda nat) :=
    {| f_algebra := Lambda_eval|}.

  (* ============================================== *)
  (* PRETTY PRINTING                                *)
  (* ============================================== *)

  Require Import String.
  Require Import Ascii.

  Global Instance MAlgebra_DTypePrint_AType T:
    FAlgebra DTypePrintName T DTypePrintR LType :=
    {| f_algebra :=
         fun rec e =>
           match e with
             | TArrow t1 t2 => append "(" ((rec t1) ++ " -> " ++ (rec t2) ++ ")")
           end
    |}.

  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR D}.

  Definition Lambda_ExpPrint (R : Set) (rec : R -> ExpPrintR)
    (e : Lambda nat R) : ExpPrintR :=
    match e with
      | Var v => fun n => append "x" (String (ascii_of_nat (v)) EmptyString)
      | App e1 e2 => fun n => append "(" ((rec e1 n) ++ ") @ (" ++ (rec e2 n) ++ ")")
      | Lam t1 f => fun n => append "\x" ((String (ascii_of_nat n) EmptyString) ++
        " : " ++ (DTypePrint _ t1) ++ ". " ++
        (rec (f n) (S n)) ++ ")")
    end.

  Global Instance MAlgebra_Print_Lambda T :
    FAlgebra ExpPrintName T ExpPrintR (Lambda nat) :=
    {| f_algebra := Lambda_ExpPrint T|}.

  Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR (F nat)}.

  Global Instance MAlgebra_ValuePrint_AType T:
  FAlgebra ValuePrintName T ValuePrintR ClosValue :=
  {| f_algebra := fun rec e =>
    match e with
      | Clos f _ => append "\x0. " (ExpPrint _ f 0)
    end |}.

  (* ============================================== *)
  (* SUBVALUE RELATION FOR LAMBDAS                  *)
  (* ============================================== *)

  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context `{ispf_SV : iSPF _ SV}.

  Inductive SubValue_Clos (A : SubValue_i V -> Prop) : SubValue_i V -> Prop :=
    SV_Clos : forall f env env',
      P2_Env (fun e e' : Value => A (mk_SubValue_i V e e')) env env' ->
      SubValue_Clos A (mk_SubValue_i _ (closure f env) (closure f env')).

  Inductive SV_Clos_S : SubValue_i V -> Set :=
    SSV_Clos : forall f env env', P2_Shape env env' ->
                 SV_Clos_S (mk_SubValue_i _ (closure f env) (closure f env')).

  Definition SV_Clos_P : forall (i : SubValue_i V), SV_Clos_S i -> Set :=
    fun i H =>
      match H in SV_Clos_S i return Set with
          SSV_Clos f env env' s => { a : _ & {b : _ & P2_Index a b s }}
      end.
  Definition SV_Clos_R (i : SubValue_i V) (s : SV_Clos_S i) (p : SV_Clos_P i s) :
    SubValue_i V.
    destruct s as [f env env' s].
    destruct p as [e [e' i]].
    apply (mk_SubValue_i V e e').
  Defined.

  Definition SV_Clos_to A i : IExt _ _ SV_Clos_R A i -> SubValue_Clos A i :=
    fun x =>
      match x with
        | iext s pf =>
          match s in SV_Clos_S i return
                ((forall p, A (SV_Clos_R i s p)) ->SubValue_Clos A i)
          with
            | SSV_Clos f env env' e =>
              fun pf =>
                SV_Clos A f env env'
                        (P2_tabulate (P := fun e e' => A (mk_SubValue_i V e e')) e
                                     (fun a b H => pf (existT _ a (existT _ b H))))
          end pf
      end.

  Definition SV_Clos_from A i : SubValue_Clos A i -> IExt _ _ SV_Clos_R A i.
    intros sv.
    destruct sv as [f env env' ps].
    constructor 1 with (s := SSV_Clos _ _ _ (P2_Env_Shape ps)).
    intros.
    destruct p as [a [b i]].
    apply (P2_lookup _ ps _ _ i).
  Defined.

  Global Instance SV_Clos_Container : IContainer SubValue_Clos :=
    {| IS    := SV_Clos_S;
       IP    := SV_Clos_P;
       IR    := SV_Clos_R;
       ifrom := SV_Clos_from;
       ito   := SV_Clos_to
    |}.
  Proof.
    intros; destruct a; simpl.
    rewrite P2_tabulate_lookup.
    reflexivity.
    intros; destruct a; destruct s; simpl.
    erewrite (P2_Shape_irrelevance _ p).
    f_equal.
    extensionality x; destruct x as [a [b idx]].
    rewrite P2_lookup_tabulate.
    reflexivity.
  Defined.

  Definition ind_alg_SV_Clos (P : SubValue_i V -> Prop)
    (P' : Env Value -> Env Value -> Prop)
    (H : forall f env env',
      P' env env' ->
      P (mk_SubValue_i _ (closure f env) (closure f env')))
    (H0 : P' nil nil)
    (H1 : forall i env env', P i -> P' env env' ->
      P' (sv_a _ i :: env) (sv_b _ i :: env'))
    i (e : SubValue_Clos P i) : P i :=
    match e in SubValue_Clos _ i return P i with
      | SV_Clos f env env' Sub_env_env' =>
        H f env env'
        ((fix P_Env_ind' (env : Env _) (env' : Env _)
          (P_env_env' : P2_Env (fun e e' => P (mk_SubValue_i _ e e')) env env') :=
          match P_env_env' in P2_Env _ As Bs return P' As Bs with
            | P2_Nil => H0
            | P2_Cons a b As Bs P_a_b P_As_Bs =>
              H1 (mk_SubValue_i _ a b) As Bs P_a_b (P_Env_ind' _ _ P_As_Bs)
          end) _ _ Sub_env_env')
    end.


  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName (Exp nat) (evalR V) (F nat)}.
  Context {WF_eval_F : @WF_FAlgebra EvalName _ _ (Lambda nat) (F nat)
    (Sub_Lambda_F nat) (MAlgebra_eval_Lambda) (eval_F)}.

  (* Continuity of Evaluation. *)

  Context {WF_SubBotValue_V : WF_Functor BotValue V Sub_BotValue_V}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.
  Context {Sub_SV_Clos_SV : Sub_iFunctor SubValue_Clos SV}.

  (* Lit case. *)

  Lemma eval_continuous_Exp_H : forall x,
    eval_continuous_Exp_P V (F nat) SV (var x).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    unfold beval, var, inject; simpl.
    rewrite out_in_inverse.
    repeat rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    caseEq (@lookup Value gamma x); unfold Value in *|-*;
      rewrite H2.
    destruct (P2_Env_lookup _ _ _ _ _ H0 _ _ H2) as [v' [lookup_v' Sub_v_v']].
    unfold Value; rewrite lookup_v'; eauto.
    unfold Value; rewrite (P2_Env_Nlookup _ _ _ _ _ H0 _ H2).
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
  Qed.

  (* Lambda case. *)

  Lemma eval_continuous_Exp_H1 : forall t1 f
    (IHf : forall a, eval_continuous_Exp_P V (F nat) SV (f a)),
    eval_continuous_Exp_P V (F nat) SV (lam t1 f).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    unfold beval, lam, inject; simpl.
    rewrite out_in_inverse.
    repeat rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    rewrite (P2_Env_length _ _ _ _ _ H0).
    apply (inject_i (subGF := Sub_SV_Clos_SV)); constructor; auto.
  Qed.

  (* App case. *)

  Context {Dis_Clos_Bot : Distinct_Sub_Functor ClosValue BotValue V}.

  Global Instance SV_invertBot_Clos :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SubValue_Clos.
  Proof.
    constructor; intros.
    unfold iAlgebra; intros.
    inversion H; subst; simpl.
    unfold SV_invertBot_P; intros.
    discriminate_inject H1.
  Qed.

  Context {SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.

  (* Inversion principles for function SubValues. *)
  Definition SV_invertClos_P (i : SubValue_i V) :=
    SubValue _ SV i /\
    forall f env, sv_a _ i = closure f env ->
      exists env', sv_b _ i = closure f env'
        /\ Sub_Environment V SV env env'.

  Inductive SV_invertClos_Name := ece_invertclosure_name.
  Context {SV_invertClos_SV :
    iPAlgebra SV_invertClos_Name SV_invertClos_P SV}.

  Global Instance SV_invertClos_refl :
    iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_refl V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertClos_P.
    inversion H; subst; simpl; intros.
    split; intros.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; simpl; auto.
    exists env; split; auto.
    apply Sub_Environment_refl; auto.
  Defined.

  Global Instance SV_invertClos_Clos :
    iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_Clos).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros.
    apply ind_alg_SV_Clos with (P' := Sub_Environment V SV).
    unfold SV_invertClos_P; intros.
    subst; simpl in *|-*.
    split; intros.
    apply (inject_i (subGF := Sub_SV_Clos_SV)); constructor; auto.
    apply inject_inject in H1; inversion H1; subst.
    exists env'; repeat split; auto.
    constructor.
    intros.
    constructor; auto.
    destruct H0 as [i' H0].
    destruct i0; apply i'.
    apply H.
  Qed.

  Variable Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV.

  Global Instance SV_invertClos_Bot :
    iPAlgebra SV_invertClos_Name SV_invertClos_P (SubValue_Bot V).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold SV_invertClos_P.
    inversion H; subst; simpl; intros.
    split; intros.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
    discriminate_inject H0.
  Defined.

  Definition SV_invertClos := ifold_ (if_algebra (iPAlgebra := SV_invertClos_SV)).

  Definition SV_invertClos'_P (i : SubValue_i V) :=
    SubValue _ SV i /\
    forall f env, sv_b _ i = closure f env ->
      sv_a _ i = bot _ \/
      (exists f,
        exists env', sv_a _ i = closure f env' /\
        Sub_Environment V SV env' env).

  Inductive SV_invertClos'_Name := ece_invertclosure'_name.
  Variable SV_invertClos'_SV : iPAlgebra SV_invertClos'_Name SV_invertClos'_P SV.

  Global Instance SV_invertClos'_refl :
    iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_refl V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertClos'_P.
    inversion H; subst; simpl; split; intros.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; auto.
    right; eexists; eexists; split; eauto.
    apply Sub_Environment_refl; eauto.
  Defined.

  Global Instance SV_invertClos'_Bot :
    iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_Bot V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertClos'_P.
    inversion H; subst; simpl; split; intros; eauto.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; reflexivity.
  Defined.

  Global Instance SV_invertClos'_Clos :
    iPAlgebra SV_invertClos'_Name SV_invertClos'_P (SubValue_Clos).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros.
    apply ind_alg_SV_Clos with (P' := Sub_Environment V SV);
      try eassumption; intros.
    unfold SV_invertClos'_P; intros; simpl; split; intros.
    apply (inject_i (subGF := Sub_SV_Clos_SV)); constructor; auto.
    right; exists f; exists env; split; auto.
    apply inject_inject in H1; inversion H1; subst.
    exact H0.
    constructor.
    constructor.
    destruct H0 as [i' H0].
    destruct i0; apply i'.
    apply H1.
  Qed.

  Definition SV_invertClos' := ifold_ (if_algebra (iPAlgebra := SV_invertClos'_SV)).

  Lemma eval_continuous_Exp_H0 : forall (e1 e2 : Exp nat)
    (IHe1 : eval_continuous_Exp_P V (F nat) SV e1)
    (IHe2 : eval_continuous_Exp_P V (F nat) SV e2),
    eval_continuous_Exp_P V (F nat) SV (app e1 e2).
  Proof.
    intros; unfold eval_continuous_Exp_P; intros.
    unfold beval, app, inject; simpl.
    rewrite out_in_inverse; simpl.
    repeat rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    unfold isClos.
    generalize (H e1 _ _ _ H0 H1) as Sub_e1_m_e1_n; intro.
    fold (Exp nat).
    caseEq (project ClosValue V
      (boundedFix m (f_algebra EvalName (FAlgebra := eval_F))
        (fun _ : Env (Names.Value V) => Names.bot V) e1 gamma)).
    apply inject_project in H2; rename H2 into Eval_m.
    destruct c.
    destruct (SV_invertClos _ Sub_e1_m_e1_n) as [_ SF']; simpl in SF';
      destruct (SF' _ _ Eval_m) as [env' [Eval_n Sub_env_env']].
    unfold beval, evalR, Exp in Eval_n; simpl in Eval_n.
    unfold beval, evalR, Exp.
    rewrite Eval_n; simpl.
    unfold closure.
    rewrite project_inject.
    eapply H; eauto.
    eapply P2_Env_insert; eauto.
    unfold isBot.
    caseEq (project BotValue V
      (boundedFix m (f_algebra EvalName (FAlgebra := eval_F))
        (fun _ : Env (Names.Value V) => Names.bot V) e1 gamma)).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor.
    eauto.
    caseEq (project ClosValue V
      (boundedFix n (f_algebra EvalName (FAlgebra := eval_F))
        (fun _ : Env (Names.Value V) => Names.bot V) e1 gamma')).
    destruct c.
    apply inject_project in H4; rename H4 into Eval_n.
    destruct (SV_invertClos' _ Sub_e1_m_e1_n) as [_ SF']; simpl in SF';
      destruct (SF' _ _ Eval_n) as [Eval_m |
      [f' [env' [Eval_m Sub_env_env']]]]; simpl in Eval_m.
    unfold beval, evalR, Exp in *|-*; rewrite Eval_m in H3.
    unfold bot in H3.
    rewrite project_inject in H3.
    discriminate.
    unfold beval, evalR, Exp in *|-*; rewrite Eval_m in H2.
    unfold closure in H2.
    rewrite project_inject in H2.
    discriminate.
    caseEq (project BotValue V
      (boundedFix n (f_algebra EvalName (FAlgebra := eval_F))
        (fun _ : Env (Names.Value V) => Names.bot V) e1 gamma')).
    destruct b.
    apply inject_project in H5; rename H5 into Eval_n.
    generalize (SV_invertBot _ _ _ Sub_e1_m_e1_n Eval_n). simpl;
    intros Eval_m; unfold beval, evalR, Exp in *|-*; rewrite Eval_m in H3.
    unfold bot, Names.bot in H3.
    rewrite project_inject in H3.
    discriminate.
    eapply (inject_i (subGF := Sub_SV_refl_SV)); constructor.
    reflexivity.
  Qed.

  Global Instance Lambda_eval_continuous_Exp :
    FPAlgebra (eval_continuous_Exp_P V (F nat) SV) (inject (Lambda nat) (F nat)).
  Proof.
    constructor; unfold PAlgebra; intros.
    apply ind_alg_Lambda.
    apply eval_continuous_Exp_H.
    apply eval_continuous_Exp_H0.
    apply eval_continuous_Exp_H1.
    assumption.
  Defined.

  (* ============================================== *)
  (* EQUIVALENCE OF EXPRESSIONS                     *)
  (* ============================================== *)

  (** SuperFunctor for Equivalence Relation. **)

  Variable EQV_E : forall A B, (eqv_i F A B -> Prop) -> eqv_i F A B -> Prop.
  Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
  Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

  Definition E_eqv A B := iFix (EQV_E A B).
  Definition E_eqvC {A B : Set} gamma gamma' e e' :=
    E_eqv _ _ (mk_eqv_i _ A B gamma gamma' e e').

  Inductive Lambda_eqv (A B : Set) (E : eqv_i F A B -> Prop) : eqv_i F A B -> Prop :=
  | Var_eqv : forall (gamma : Env _) gamma' n a b,
    lookup gamma n = Some a -> lookup gamma' n = Some b ->
    Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' (var a) (var b))
  | App_eqv : forall (gamma : Env _) gamma' a b a' b',
    E (mk_eqv_i _ _ _ gamma gamma' a a') ->
    E (mk_eqv_i _ _ _ gamma gamma' b b') ->
    Lambda_eqv A B E (mk_eqv_i _ _ _ gamma gamma' (app a b) (app a' b'))
  | Lam_eqv : forall (gamma : Env _) gamma' f g t,
    (forall (a : A) (b : B), E (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))) ->
    Lambda_eqv _ _ E (mk_eqv_i _ _ _ gamma gamma' (lam t f) (lam t g)).

  Inductive Lambda_eqv_S (A B : Set) : eqv_i F A B -> Set :=
  | SVar_eqv : forall (gamma : Env _) gamma' n a b,
    lookup gamma n = Some a -> lookup gamma' n = Some b ->
    Lambda_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (var a) (var b))
  | SApp_eqv : forall (gamma : Env _) gamma' a b a' b',
    Lambda_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (app a b) (app a' b'))
  | SLam_eqv : forall (gamma : Env _) gamma' f g t,
    Lambda_eqv_S A B (mk_eqv_i _ _ _ gamma gamma' (lam t f) (lam t g)).

  Definition Lambda_eqv_P (A B : Set) (i : eqv_i F A B) (s : Lambda_eqv_S A B i) : Set.
    destruct s.
    apply Empty_set.
    apply ((unit + unit)%type).
    apply ((A * B)%type).
  Defined.

  Definition Lambda_eqv_R (A B : Set) (i : eqv_i F A B)
             (s : Lambda_eqv_S A B i)
             (p : Lambda_eqv_P A B i s) : eqv_i F A B.
    destruct s; simpl in p.
    destruct p.
    destruct p as [p|p].
    apply (mk_eqv_i _ _ _ gamma gamma' a a').
    apply (mk_eqv_i _ _ _ gamma gamma' b b').
    destruct p.
    apply (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b)).
  Defined.

  Definition Lambda_eqv_to (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    IExt _ _ (Lambda_eqv_R A B) C i -> Lambda_eqv A B C i.
  Proof.
    intros x; destruct x; destruct s; simpl in pf.
    constructor 1 with (n := n); auto.
    constructor 2.
    apply (pf (inl tt)).
    apply (pf (inr tt)).
    constructor 3.
    intros.
    apply (pf (a , b)).
  Defined.

  Definition Lambda_eqv_from (A B : Set) (C : eqv_i F A B -> Prop) (i : eqv_i F A B) :
    Lambda_eqv A B C i -> IExt _ _ (Lambda_eqv_R A B) C i.
  Proof.
    intros x; destruct x.
    constructor 1 with (s := SVar_eqv _ _ gamma gamma' n a b H H0); simpl.
    intro p; destruct p.
    constructor 1 with (s := SApp_eqv _ _ gamma gamma' a b a' b'); simpl.
    intro p; destruct p as [p|p]; auto.
    constructor 1 with (s := SLam_eqv _ _ gamma gamma' f g t); simpl.
    intro p; destruct p; auto.
  Defined.

  Global Instance Lambda_eqv_Container (A B : Set) : IContainer (Lambda_eqv A B) :=
    {| IS    := Lambda_eqv_S A B;
       IP    := Lambda_eqv_P A B;
       IR    := Lambda_eqv_R A B;
       ifrom := Lambda_eqv_from A B;
       ito   := Lambda_eqv_to A B
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl; f_equal;
      extensionality x; destruct x; try destruct u; reflexivity.
  Defined.

  Definition ind_alg_Lambda_eqv
    (A B : Set)
    (P : eqv_i F A B -> Prop)
    (H : forall gamma gamma' n a b lookup_a lookup_b,
      P (mk_eqv_i _ _ _ gamma gamma' (var a) (var b)))
    (H0 : forall gamma gamma' a b a' b'
      (IHa : P (mk_eqv_i _ _ _ gamma gamma' a a'))
      (IHb : P (mk_eqv_i _ _ _ gamma gamma' b b')),
      P (mk_eqv_i _ _ _ gamma gamma' (app a b) (app a' b')))
    (H1 : forall gamma gamma' f g t
      (IHf : forall a b, P (mk_eqv_i _ _ _ (insert _ a gamma) (insert _ b gamma') (f a) (g b))),
      P (mk_eqv_i _ _ _ gamma gamma' (lam t f) (lam t g)))
    i (e : Lambda_eqv A B P i) : P i :=
    match e in Lambda_eqv _ _ _ i return P i with
      | Var_eqv gamma gamma' n a b lookup_a lookup_b =>
        H gamma gamma' n a b lookup_a lookup_b
      | App_eqv gamma gamma' a b a' b' eqv_a_a' eqv_b_b' =>
        H0 gamma gamma' a b a' b' eqv_a_a' eqv_b_b'
      | Lam_eqv gamma gamma' f g t eqv_f_g  =>
        H1 gamma gamma' f g t eqv_f_g
    end.

  Variable Sub_Lambda_eqv_EQV_E : forall A B,
    Sub_iFunctor (Lambda_eqv A B) (EQV_E A B).

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) (F (typeofR D))}.

  (* ============================================== *)
  (* WELL-FORMED FUNCTION VALUES                    *)
  (* ============================================== *)

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{ispf_WFV : iSPF _ WFV}.
  Variable typeof_rec : Exp (typeofR D) -> typeofR D.
  (** Functions are well-formed **)

  Inductive WFValue_Clos
    (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop :=
  | WFV_Clos : forall (f : option DType -> Names.Exp _) f' env gamma gamma'
    (t1 t2 : DType) v T,
    v = closure (f' (List.length gamma)) env ->
    T = tarrow t1 t2 ->
    (forall a b, E_eqvC (insert _ a gamma) (insert _ b gamma') (f a) (f' b)) ->
    (forall n b, lookup gamma' n = Some b ->
      exists T, lookup gamma b = Some T) ->
    List.length gamma = List.length gamma' ->
    P2_Env (fun v T => match T with
                         | Some T => WFV (mk_WFValue_i _ _ v T)
                         | _ => False
                       end) env gamma ->
    (forall n b, lookup gamma' n = Some b -> b = n) ->
    typeof_rec (f (Some t1)) = Some t2 ->
    WFValue_Clos  WFV (mk_WFValue_i D V v T).

  Inductive WFValue_Clos_S : WFValue_i D V -> Set :=
  | SWFV_Clos : forall (f : option DType -> Names.Exp _) f' env gamma gamma'
    (t1 t2 : DType) v T,
    v = closure (f' (List.length gamma)) env ->
    T = tarrow t1 t2 ->
    (forall a b, E_eqvC (insert _ a gamma) (insert _ b gamma') (f a) (f' b)) ->
    (forall n b, lookup gamma' n = Some b ->
      exists T, lookup gamma b = Some T) ->
    List.length gamma = List.length gamma' ->
    forall (s : P2_Shape env gamma),
    (forall a b, P2_Index a b s -> exists T, b = Some T) ->
    (forall n b, lookup gamma' n = Some b -> b = n) ->
    typeof_rec (f (Some t1)) = Some t2 ->
    WFValue_Clos_S (mk_WFValue_i D V v T).

  Definition WFValue_Clos_P (i : WFValue_i D V) (s : WFValue_Clos_S i) : Type :=
    match s with
      | SWFV_Clos _ _ env gamma _ _ _ _ _ _ _ _ _ _ s _ _ _ =>
        {a : _ & {b : DType & P2_Index a (Some b) s }}
    end.

  Definition WFValue_Clos_R (i : WFValue_i D V)
           (s : WFValue_Clos_S i)
           (p : WFValue_Clos_P i s) : WFValue_i D V.
    destruct s; simpl in *.
    destruct p as [a [b idx]].
    apply (mk_WFValue_i _ _ a b).
  Defined.

  Definition WFValue_Clos_to (A : WFValue_i D V -> Prop) (i : WFValue_i D V) :
    IExt _ _ WFValue_Clos_R A i -> WFValue_Clos A i.
    intros x; destruct x; destruct s; simpl in pf.
    apply (WFV_Clos _ f f' env gamma gamma' t1 t2 v T); auto.
    apply (P2_tabulate s).
    intros.
    destruct b.
    apply (pf (existT _ a (existT _ d H))).
    generalize (e4 _ _ H).
    intros; destruct H0; discriminate.
  Defined.

  Definition WFValue_Clos_from (A : WFValue_i D V -> Prop) (i : WFValue_i D V) :
    WFValue_Clos A i -> IExt _ _ WFValue_Clos_R A i.
    intros x; destruct x.
    assert (P2_Shape env gamma) as ps.
    apply (P2_Env_Shape H4).
    constructor 1 with (s := SWFV_Clos f f' env gamma gamma' t1 t2 v T H H0 H1 H2 H3 ps
                      (fun a b =>
                         match b return (P2_Index a b ps -> exists T0 : DType, b = Some T0) with
                           | Some T => fun idx => ex_intro _ T eq_refl
                           | None => fun idx => False_rec _ (P2_lookup ps H4 _ _ idx)
                         end
                      ) H5 H6); simpl; intro p.
    destruct p as [a [b idx]].
    apply (P2_lookup _ H4 _ _ idx).
  Defined.

  Lemma e4_irrelevance {A B : Set} {As Bs} (s : P2_Shape As Bs)
        (f g : forall (a : Fix V) (b : option DType),
                 P2_Index a b s -> exists T : DType, b = Some T)
  : f = g.
  Proof.
    extensionality a; extensionality b; extensionality idx.
    destruct (f a b idx); destruct (g a b idx); subst.
    dependent destruction e0; reflexivity.
  Defined.

  Global Instance WFValue_Clos_Container : IContainer WFValue_Clos :=
    {| IS    := WFValue_Clos_S;
       IP    := WFValue_Clos_P;
       IR    := WFValue_Clos_R;
       ifrom := WFValue_Clos_from;
       ito   := WFValue_Clos_to
    |}.
  Proof.
    intros; destruct a; simpl.
    f_equal.
    rewrite <- (P2_tabulate_lookup p (P2_Env_Shape p)) at 2.
    f_equal.
    extensionality a; extensionality b; extensionality idx.
    destruct b; simpl.
    reflexivity.
    destruct (P2_lookup (P2_Env_Shape p) p a None idx).
    intros; destruct a; destruct s; simpl.
    rewrite (P2_Shape_irrelevance _ s).
    erewrite (@e4_irrelevance Value (option DType) _ _ s _ e4).
    f_equal.
    extensionality p.
    destruct p as [a [b idx]].
    rewrite P2_lookup_tabulate.
    reflexivity.
  Defined.

  Context {WF_typeof_F : forall T, @WF_FAlgebra TypeofName T (typeofR D) _ _
    (Sub_Lambda_F _) (MAlgebra_typeof_Lambda T) (Typeof_F _)}.
  Context {WF_Value_continous_alg :
    iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

  Definition ind_alg_WFV_Clos
    (P : WFValue_i D V -> Prop)
    (P' : Env Value -> Env (option DType) -> Prop)
    (H : forall f f' env gamma gamma' t1 t2 v T
      v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma'
      P2_env lookup_gamma'' type_of_f,
      P' env gamma ->
      P (mk_WFValue_i _ _ v T))
    (H0 : P' nil nil)
    (H1 : forall a b env env',
      match b with
        | Some T => P {| wfv_a := a; wfv_b := T |}
        | None => False
      end -> P' env env' ->
      P' (a :: env) (b :: env'))
    i (e : WFValue_Clos  P i) : P i :=
    match e in WFValue_Clos _ i return P i with
      | WFV_Clos f f' env gamma gamma' t1 t2 v T
      v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma'
      P2_env lookup_gamma'' type_of_f =>
      H f f' env gamma gamma' t1 t2 v T
      v_eq T_e1 eqv_f_f' lookup_gamma' len_gamma_gamma'
      P2_env lookup_gamma'' type_of_f
      ((fix P_Env_ind' (env : Env Value) (env' : Env (option DType))
        (P_env_env' : P2_Env (fun v T => match T with
                                           | Some T => P (mk_WFValue_i _ _ v T)
                                           | _ => False
                                         end) env env') :=
        match P_env_env' in P2_Env _ As Bs return P' As Bs with
          | P2_Nil => H0
          | P2_Cons a b As Bs P_a_b P_As_Bs =>
            H1 a b As Bs P_a_b (P_Env_ind' _ _ P_As_Bs)
        end) env gamma P2_env)
    end.

  Variable Sub_WFV_Clos_WFV : Sub_iFunctor WFValue_Clos WFV.
  Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

  (* Inversion principles for Well-formed natural numbers. *)
  Definition WF_invertClos_P (i : WFValue_i D V) :=
    WFValue _ _ WFV i /\
    forall t1 t2, wfv_b _ _ i = tarrow t1 t2 ->
    WFValue_Clos  (iFix WFV) i \/ WFValue_Bot _ _ (iFix WFV) i.

  Inductive WF_invertClos_Name := wfv_invertclosure_name.
  Context {WF_invertClos_WFV :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P ) WFV}.

  Global Instance WF_invertClos_Clos  :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P ) (WFValue_Clos ).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
      P2_Env (fun v T => match T with
                           | Some T => WFValueC _ _ WFV v T
                           | _ => False
                         end)).
    inversion H; subst; simpl; intros; split.
    eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
      econstructor 1; simpl in *|-*; eauto.
    left; econstructor 1; simpl in *|-*; eauto; try congruence.
    rewrite T_e1 in H1; apply inject_inject in H1.
    injection H1; intros; congruence.
    constructor.
    constructor.
    destruct b; destruct H0; eauto.
    assumption.
    exact H.
  Defined.

  Global Instance WF_invertClos_Bot  :
    iPAlgebra WF_invertClos_Name (WF_invertClos_P ) (WFValue_Bot _ _).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
    right; constructor; reflexivity.
  Defined.

  Definition WF_invertClos  := ifold_ (if_algebra (iPAlgebra := WF_invertClos_WFV )).

  Definition WF_invertClos'_P  (i : WFValue_i D V) :=
    WFValue _ _ WFV i /\
    forall v : ClosValue _, wfv_a _ _ i = inject _ _ v ->
    WFValue_Clos  (iFix WFV) i.

  Inductive WF_invertClos'_Name := wfv_invertclosure'_name.
  Context {WF_invertClos'_WFV :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) WFV}.

  Global Instance WF_invertClos'_Clos  :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) (WFValue_Clos ).
  Proof.
    constructor; intros.
    unfold iAlgebra; intros; apply (ind_alg_WFV_Clos ) with (P' :=
      P2_Env (fun v T => match T with
                           | Some T => WFValueC _ _ WFV v T
                           | _ => False
                         end)).
    inversion H; subst; simpl; intros; split.
    eapply (inject_i (subGF := Sub_WFV_Clos_WFV ));
      econstructor 1;
      simpl in *|-*; eauto.
    intros; econstructor 1; simpl in *|-*; eauto.
    left; econstructor; simpl in *|-*; eauto; try congruence.
    intros; constructor; auto.
    destruct b; destruct H0; auto.
    assumption.
  Defined.

  Global Instance WF_invertClos'_Bot  :
    iPAlgebra WF_invertClos'_Name (WF_invertClos'_P ) (WFValue_Bot _ _).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold WF_invertClos'_P.
    inversion H; subst; simpl; intros.
    split.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
    intros; discriminate_inject H0.
  Defined.

  Definition WF_invertClos'  :=
    ifold_ (if_algebra (iPAlgebra := WF_invertClos'_WFV )).

  Global Instance WFV_Value_continuous_Clos :
    iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SubValue_Clos.
  Proof.
    constructor; unfold iAlgebra; intros.
    eapply ind_alg_SV_Clos with (P' := fun env env' => forall gamma,
      P2_Env (fun (v0 : Names.Value V) (T0 : option (Names.DType D)) =>
        match T0 with
          | Some T1 => iFix WFV {| wfv_a := v0; wfv_b := T1 |}
          | None => False
        end) env' gamma ->
      P2_Env (fun (v0 : Names.Value V) (T0 : option (Names.DType D)) =>
        match T0 with
          | Some T1 => iFix WFV {| wfv_a := v0; wfv_b := T1 |}
          | None => False
        end) env gamma); try eassumption; auto.
    unfold WF_Value_continuous_P; simpl; intros.
    destruct (WF_invertClos'  _ H1) as [_ H5]; simpl in H5;
      generalize (H5 _ eq_refl); clear H5.
    intros H1'; inversion H1'; subst.
    apply inject_inject in H4; injection H4; intros; subst; clear H4.
    apply (inject_i (subGF := (Sub_WFV_Clos_WFV ))).
    econstructor 1 with (f' := f') (env := env) (gamma := gamma); auto.
    intros; inversion H2; subst.
    econstructor.
    destruct b; try destruct H5.
    apply H0; auto.
    apply H1; auto.
  Defined.

  Lemma isClos_closure : forall t1 f, isClos (closure t1 f) =
    Some (t1, f).
  Proof.
    intros; unfold isClos, closure. rewrite project_inject; reflexivity.
  Qed.

  Lemma isClos_bot :
    isClos (bot _) = None.
  Proof.
    unfold isClos; simpl.
    crush_project.
  Qed.

  Lemma isBot_closure :
    forall t1 f, isBot _ (closure t1 f) = false.
  Proof.
    intros; unfold isBot.
    crush_project.
  Qed.

  Global Instance Lambda_eqv_eval_soundness_alg : forall eval_rec,
    iPAlgebra soundness_XName
    (soundness_X'_P D V F EQV_E WFV
      typeof_rec eval_rec
      (f_algebra TypeofName (FAlgebra := Typeof_F _))
      (f_algebra EvalName (FAlgebra := eval_F))) (Lambda_eqv _ _).
  Proof.
    constructor; unfold iAlgebra; intros.
    apply ind_alg_Lambda_eqv; try eassumption;
    unfold soundness_X'_P, eval_alg_Soundness_P; simpl; intros.
    (* Var Case *)
    split.
    apply inject_i; econstructor; eauto.
    intros; unfold var, inject; rewrite out_in_inverse; simpl.
    rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]];
      simpl in *|-*.
    rewrite (WF_gamma' _ _ lookup_b) in *|-*.
    destruct (P2_Env_lookup' _ _ _ _ _ WF_gamma'' _ _ lookup_a) as [v [lookup_v WF_v]];
        unfold Value; rewrite lookup_v.
    destruct a; eauto.
    rename H0 into typeof_d.
    unfold var, inject in typeof_d; rewrite out_in_inverse in typeof_d;
      rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)) in typeof_d;
        simpl in typeof_d; injection typeof_d; intros; subst; auto.
    destruct WF_v.
    (* app case *)
    destruct (IHa IH) as [eqv_a _]; destruct (IHb IH) as [eqv_b _].
    split.
    apply inject_i; econstructor 2; simpl; eauto.
    intros; unfold app, inject; rewrite out_in_inverse; simpl.
    rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    rename H0 into typeof_e.
    unfold app, inject in typeof_e; rewrite out_in_inverse in typeof_e;
      rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)) in typeof_e;
        simpl in typeof_e.
    caseEq (typeof_rec a); rename H0 into typeof_a;
      rewrite typeof_a in typeof_e; try discriminate.
    caseEq (typeof_rec b); rename H0 into typeof_b;
      rewrite typeof_b in typeof_e; try discriminate.
    caseEq (isTArrow d); rewrite H0 in typeof_e; try discriminate.
    destruct p as [t1 t2].
    caseEq (eq_DType D t1 d0); rename H1 into eq_t1;
      rewrite eq_t1 in typeof_e; try discriminate; injection typeof_e; intros; subst; clear typeof_e.
    apply eq_DType_eq in eq_t1; subst.
    generalize (IH a _ _ _ WF_gamma'' d eqv_a typeof_a); intros WF_a.
    unfold isTArrow in H0.
    caseEq (project LType D d); rename H1 into typeof_d;
      rewrite typeof_d in H0; try discriminate; destruct l.
    inversion H0; subst.
    apply inject_project in typeof_d.
    destruct (WF_invertClos  _ WF_a) as [_ VWF_a']; clear WF_a;
      destruct (VWF_a' _ _ typeof_d) as [WF_a' | WF_a']; inversion WF_a'; subst.
    rewrite H3, isClos_closure.
    apply inject_inject in H4; inversion H4; subst.
    eapply IH; simpl; eauto.
    eapply WF_eqv_environment_P_insert; repeat split; eauto.
    rewrite <- H7.
    apply H5.
    rewrite H2.
    generalize isClos_bot; unfold bot, Names.bot; intro H'; rewrite H'.
    generalize isBot_bot; unfold bot, Names.bot; intro H''; rewrite H''.
    apply (inject_i (subGF := Sub_WFV_Bot_WFV)); constructor; auto.
    (* lam case *)
    split; intros.
    generalize (fun a b => proj1 (IHf a b IH)); intro IHf'.
    apply inject_i; econstructor 3; eauto.
    unfold lam, inject in H0; rewrite out_in_inverse in H0;
      rewrite (wf_mixin (WF_Mixin := WF_typeof_F _)) in H0; simpl in H0.
    caseEq (typeof_rec (f (Some t)));
      rename H1 into typeof_f; unfold DType, Names.DType in *|-*; rewrite typeof_f in H0; try discriminate.
    injection H0; intros; subst; clear H0.
    unfold lam, inject at 1; rewrite out_in_inverse, (wf_mixin (WF_Mixin := WF_eval_F)); simpl.
    destruct WF_gamma'' as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
    apply (inject_i (subGF := Sub_WFV_Clos_WFV)).
    rewrite (P2_Env_length _ _ _ _ _ WF_gamma''); simpl.
    eapply WFV_Clos with (f' := g) (gamma := gamma).
    reflexivity.
    reflexivity.
    intros; apply (proj1 (IHf a b IH)); auto.
    auto.
    auto.
    auto.
    auto.
    auto.
  Defined.

End Lambda.
