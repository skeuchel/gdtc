Require Import Coq.Program.Equality.
Require Import FJ_tactics.
Require Import List.
Require Import Containers.
Require Import Functors.
Require Import Polynomial.
Require Import Names.
Require Import FunctionalExtensionality.

Section Arith.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (* The Arithmetic Type. *)
  Inductive AType (A : Set) : Set :=
    TNat : AType A.

  (* Global Instance AType_Iso : Iso AType (K unit) := *)
  (*   {| fromIso := fun A x => tt; *)
  (*      toIso := fun A x => TNat A *)
  (*   |}. *)
  (* Proof. *)
  (*   intros; destruct a; reflexivity. *)
  (*   intros; destruct a; reflexivity. *)
  (* Qed. *)

  (* Global Instance AType_Container : Container AType := *)
  (*   ContainerIso AType_Iso. *)

  Global Instance AType_Polynomial : Polynomial AType :=
    {| PCode := U;
       pto   := fun _ x => TNat _;
       pfrom := fun _ x => eu _
    |}.
  Proof.
    intros A a; destruct a; reflexivity.
    intros A a; dependent destruction a; reflexivity.
  Defined.

  Global Instance AType_Container : Container AType | 6 :=
    PolynomialContainer AType.

  Variable D : Set -> Set.
  Context `{spf_D : SPF D}.
  Definition DType := DType D.
  Context {Sub_AType_D  : AType :<: D}.

  (* Constructor . *)
  Context {WF_Sub_AType_D : WF_Functor _ _ Sub_AType_D}.

  Definition tnat : DType := inject (TNat _).

  (* Induction Principle for Nat Types. *)
  Definition ind_alg_AType
    (P : DType -> Prop)
    (H : P tnat) : PAlgebra (inject' AType) P :=
    fun xs Axs =>
      match xs return P (inject' AType xs) with
        | TNat => H
      end.

  (* Type Equality Section. *)
  Definition isTNat : DType -> bool :=
   fun typ =>
     match project typ with
      | Some TNat => true
      | None      => false
     end.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  Inductive Arith (a : Set) : Set :=
  | Lit : nat -> Arith a
  | Add : a -> a -> Arith a.

  (* Inductive ArithS := SLit : nat -> ArithS | SAdd. *)
  (* Inductive ArithP : ArithS -> Set := *)
  (* | PAdd1 : ArithP SAdd *)
  (* | PAdd2 : ArithP SAdd. *)

  (* Definition fromArith (A : Set) (x : Arith A) : Ext ArithS ArithP A. *)
  (*   destruct x. *)
  (*   apply ext with (s := SLit n). *)
  (*   intro p. *)
  (*   inversion p. *)
  (*   apply ext with (s := SAdd). *)
  (*   intro p. *)
  (*   inversion p. *)
  (*   apply a. *)
  (*   apply a0. *)
  (* Defined. *)

  (* Definition toArith (A : Set) (x : Ext ArithS ArithP A) : Arith A := *)
  (*   match x with *)
  (*     | ext s pf => *)
  (*       match s as s return ((ArithP s -> A) -> Arith A) with *)
  (*         | SLit n => fun pf => Lit A n *)
  (*         | SAdd   => fun pf => Add A (pf PAdd1) (pf PAdd2) *)
  (*       end pf *)
  (*   end. *)

  (* Global Instance Arith_Container : Container Arith := *)
  (*   {| Shape    := ArithS; *)
  (*      Position := ArithP; *)
  (*      from     := fromArith; *)
  (*      to       := toArith |}. *)
  (* Proof. *)
  (*   intros A x. *)
  (*   destruct x; reflexivity. *)
  (*   intros A x. *)
  (*   destruct x as [[] pf]; simpl; *)
  (*     f_equal; extensionality p; dependent destruction p; *)
  (*     reflexivity. *)
  (* Defined. *)

  Global Instance Arith_Iso : Iso Arith (K nat :+: Id :*: Id) :=
    {| fromIso := fun A x => match x with
                               | Lit n => inl n
                               | Add x y => inr (x,y)
                             end;
       toIso   := fun A x => match x with
                               | inl n => Lit _ n
                               | inr (x,y) => Add _ x y
                             end
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a as [n|[x y]]; reflexivity.
  Defined.

  Global Instance Arith_Container : Container Arith :=
    ContainerIso Arith_Iso.

  Variable F : Set -> Set.
  Context `{spf_F : SPF F}.
  Definition Exp := Exp F.
  Context {Sub_Arith_F : Arith :<: F}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_Arith_F : WF_Functor _ _ Sub_Arith_F}.
  Definition lit (n : nat) : Exp := inject (Lit _ n).
  Definition add (m n : Exp) : Exp :=  inject (Add _ m n).

  (* Induction Principles for Arith. *)
  Definition ind_alg_Arith
    (P : Fix' F -> Prop)
    (Hlit : forall n, P (lit n))
    (Hadd : forall m n, P m -> P n -> P (add m n))
      : PAlgebra (inject' Arith) P :=
    fun xs => match xs return (All P xs -> P (inject xs)) with
                | Lit n => fun Axs => Hlit n
                | Add m n => fun Axs => Hadd m n (Axs (inl _ tt)) (Axs (inr _ tt))
                (* | Add m n => fun Axs => Hadd m n (Axs PAdd1) (Axs PAdd2) *)
              end.

  Definition ind2_alg_Arith
    {E E' : Set -> Set}
    `{SPF_E : SPF E}
    `{SPF_E' : SPF E'}
    {Sub_Arith_E : Arith :<: E}
    {Sub_Arith_E' : Arith :<: E'}
    (P : (Fix' E) * (Fix' E') -> Prop)
    (Hlit : forall n, P (inject2 (Lit _ n)))
    (Hadd : forall m n (IHm : P m) (IHn : P n),
      P (inject2 (Add _ m n)))
  : PAlgebra (inject2 (F := Arith) (G := E) (G' := E')) P :=
    fun xs => match xs return (All P xs -> P (inject2 xs)) with
                | Lit n => fun Axs => Hlit n
                | Add m n => fun Axs => Hadd m n (Axs (inl _ tt)) (Axs (inr _ tt))
                (* | Add m n => fun Axs => Hadd m n (Axs PAdd1) (Axs PAdd2) *)
              end.

  (* ============================================== *)
  (* TYPING                                         *)
  (* ============================================== *)

  (* Typing Arithmetic Expressions. *)

  Definition Arith_typeof (R : Set) (rec : R -> typeofR D)
     (e : Arith R) : typeofR D :=
    match e with
      | Lit n => Some tnat
      | Add m n => match (rec m), (rec n) with
                     | Some T1, Some T2 =>
                       match isTNat T1, isTNat T2 with
                         | true, true => Some tnat
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

  Global Instance NatValue_Iso : Iso NatValue (K nat) :=
    {| fromIso := fun A x => match x with
                               | VI n => n
                             end;
       toIso := fun A x => VI A x
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; reflexivity.
  Defined.

  Global Instance NatValue_Container : Container NatValue
    := ContainerIso NatValue_Iso.

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {PFun_V : PFunctor V}.
  Context {spf_V : SPF V}.
  Definition Value := Value V.
  Context {Sub_NatValue_V : NatValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_Sub_NatValue_F : WF_Functor _ _ Sub_NatValue_V}.

  Definition vi (n : nat) : Value := inject (VI _ n).

  (* Constructor Testing for Arithmetic Values. *)

  Definition isVI : Fix' V -> option nat :=
    fun exp =>
      match project exp with
        | Some (VI n) => Some n
        | None        => None
      end.

   Context {Sub_StuckValue_V : StuckValue :<: V}.
   Definition stuck : nat -> Value := stuck _.

  Lemma isVI_vi (n : nat) : isVI (vi n) = Some n.
  Proof.
    unfold isVI, vi.
    rewrite project_inject.
    reflexivity.
  Qed.

  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V}.
  Context {Dis_VI_Bot : Distinct_Sub_Functor NatValue BotValue V}.

  Lemma isVI_bot : isVI (bot _) = None.
  Proof.
    unfold isVI; crush_project.
  Qed.

  Lemma isBot_vi (n : nat) : isBot V (vi n) = false.
  Proof.
    unfold isBot; crush_project.
  Qed.

  (* ============================================== *)
  (* EVALUATION                                     *)
  (* ============================================== *)


  (* Evaluation Algebra for Arithemetic Expressions. *)

  Definition Arith_eval (R : Set) (rec : R -> evalR V)
    (e : Arith R) : evalR V :=
    match e with
      | Lit n   => fun _ => vi n
      | Add m n =>
        fun env =>
          let m' := (rec m env) in
          let n' := (rec n env) in
          match isVI m', isVI n' with
            | Some m', Some n' => vi (m' + n')
            | _, _ =>
              if isBot _ m'
              then bot _
              else if isBot _ n'
                   then bot _
                   else stuck 4
          end
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
    {| f_algebra :=
         fun rec e =>
           match e with
             | Lit n => fun i => String (ascii_of_nat (n + 48)) EmptyString
             | Add m n => fun i => append "(" ((rec m i) ++ " + " ++ (rec n i) ++ ")")
           end |}.

  Global Instance MAlgebra_ValuePrint_AType T :
    FAlgebra ValuePrintName T ValuePrintR NatValue :=
    {| f_algebra :=
         fun rec e =>
           match e with
             | VI n => String (ascii_of_nat (n + 48)) EmptyString
           end |}.

  (* ============================================== *)
  (* TYPE SOUNDNESS                                 *)
  (* ============================================== *)

  Context {eval_F : FAlgebra EvalName Exp (evalR V) F}.
  Context {WF_eval_F : WF_FAlgebra EvalName _ _ Arith F
    (MAlgebra_eval_Arith _) eval_F}.

  (* Continuity of Evaluation. *)

  Context {SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop}.
  Context `{iSPF_F : iSPF _ SV}.
  Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

  (* Lit case. *)

  Lemma eval_continuous_Exp_H : forall n,
    eval_continuous_Exp_P V F SV (lit n).
  Proof.
    unfold eval_continuous_Exp_P; intros.
    unfold beval, lit; simpl; unfold inject.
    rewrite out_in_inverse.
    repeat rewrite (@wf_mixin _ _ _ _ _ _ _ WF_eval_F); simpl.
    apply inject_i.
    constructor.
    reflexivity.
  Qed.

  (* Add case. *)

  (* Inversion principles for natural number SubValues. *)
  Definition SV_invertVI_P (i : SubValue_i V) :=
    forall n, sv_a _ i = vi n ->
      sv_b _ i = vi n.

  Inductive SV_invertVI_Name := ece_invertvi_name.
  Context {SV_invertVI_SV :
    iPAlgebra SV_invertVI_Name SV_invertVI_P SV}.

  Global Instance SV_invertVI_refl :
    iPAlgebra SV_invertVI_Name SV_invertVI_P (SubValue_refl V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVI_P.
    inversion H; subst; simpl; congruence.
  Defined.

  Lemma SV_invertVI_default : forall V'
    (Fun_V' : Functor V')
    (SV' : (SubValue_i V -> Prop) -> SubValue_i V -> Prop)
    (sub_V'_V : V' :<: V)
    (WF_V' : WF_Functor V' V sub_V'_V),
    (forall (i : SubValue_i V) (H : SV' SV_invertVI_P i),
      exists v', sv_a _ i = inject v') ->
    Distinct_Sub_Functor NatValue V' V ->
    iPAlgebra SV_invertVI_Name SV_invertVI_P SV'.
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVI_P.
    destruct (H _ H1) as [v' eq_v'].
    intros; rewrite eq_v' in H2.
    discriminate_inject H2.
  Defined.

  Global Instance SV_invertVI_Bot :
    iPAlgebra SV_invertVI_Name SV_invertVI_P (SubValue_Bot V).
  Proof.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertVI_P.
    inversion H; subst; simpl; intros.
    discriminate_inject H0.
  Defined.

  Definition SV_invertVI := ifold_ (if_algebra (iPAlgebra := SV_invertVI_SV)).

  Definition SV_invertVI'_P (i : SubValue_i V) :=
    forall n, sv_b _ i = vi n ->
      sv_a _ i = vi n \/ sv_a _ i = bot _.

  Inductive SV_invertVI'_Name := ece_invertvi'_name.
  Context {SV_invertVI'_SV :
    iPAlgebra SV_invertVI'_Name SV_invertVI'_P SV}.

  Global Instance SV_invertVI'_refl :
    iPAlgebra SV_invertVI'_Name SV_invertVI'_P (SubValue_refl V).
  Proof.
    constructor; unfold iAlgebra, SV_invertVI'_P; intros.
    inversion H; subst; auto.
  Defined.

  Global Instance SV_invertVI'_Bot :
    iPAlgebra SV_invertVI'_Name SV_invertVI'_P (SubValue_Bot V).
  Proof.
    constructor; unfold iAlgebra, SV_invertVI'_P; intros.
    inversion H; subst; auto.
  Defined.

  Definition SV_invertVI' := ifold_ (if_algebra (iPAlgebra := SV_invertVI'_SV)).

  (* End Inversion principles for SubValue.*)

  Context {SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name (SV_invertBot_P V) SV}.

  Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.

  Lemma project_bot_vi :
    forall n,
      project (F := V) (G := BotValue) (vi n) = None.
  Proof.
    intros; crush_project.
  Qed.

  Lemma project_vi_bot : project (F := V) (G := NatValue) (bot _) = None.
  Proof.
    intros; crush_project.
  Qed.

  Lemma project_vi_vi :
    forall n,
      project (F := V) (G := NatValue) (vi n) = Some (VI _ n).
  Proof.
    intros; unfold vi; rewrite project_inject; reflexivity.
  Qed.

  Lemma eval_continuous_Exp_H0 : forall
    (m n : Fix' F)
    (IHm : eval_continuous_Exp_P V F SV m)
    (IHn : eval_continuous_Exp_P V F SV n),
    eval_continuous_Exp_P V F SV (add m n).
    unfold eval_continuous_Exp_P; intros.
    unfold add, inject; simpl_beval.
    generalize (H m _ _ _ H0 H1); simpl; intros SubV_m.
    generalize (H n _ _ _ H0 H1); simpl; intros SubV_n.
    unfold isVI at 1.
    caseEq (project (G := NatValue) (beval V F m0 m gamma)).
    destruct n1.
    apply inject_project in H2; fold (vi n1) in H2; rename H2 into Eval_m.
    generalize (SV_invertVI _ SubV_m _ Eval_m); simpl; intros Eval_m'.
    rewrite Eval_m, Eval_m', isVI_vi, isBot_vi.
    unfold isVI at 1.
    caseEq (project (G := NatValue) (beval V F m0 n gamma)).
    destruct n2.
    apply inject_project in H2; rename H2 into Eval_n.
    generalize (SV_invertVI _ SubV_n _ Eval_n); simpl; intros Eval_n'.
    rewrite Eval_n', isVI_vi.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    unfold isBot at 1.
    caseEq (project (G := BotValue) (beval V F m0 n gamma)).
    destruct b.
    apply inject_i; constructor; reflexivity.
    unfold isVI at 1.
    caseEq (project (G := NatValue) (beval V F n0 n gamma')).
    destruct n2.
    apply inject_project in H4; rename H4 into Eval_n'.
    destruct (SV_invertVI' _ SubV_n _ Eval_n') as [n_eq_vi | n_eq_bot];
      simpl in *|-.
    rewrite n_eq_vi in H2; unfold vi in H2;
      rewrite project_inject in H2; discriminate.
    rewrite n_eq_bot in H3; unfold bot in H3;
      rewrite project_inject in H3; discriminate.
    unfold isBot.
    caseEq (project (G := BotValue) (beval V F n0 n gamma')).
    destruct b.
    apply inject_project in H5; rename H5 into Eval_n'.
    generalize (SV_invertBot _ SV _ SubV_n Eval_n').
    unfold bot at 1; simpl; intros Eval_n;
      rewrite Eval_n, project_inject in H3; discriminate.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
    unfold isBot at 1.
    caseEq (project (G := BotValue) (beval V F m0 m gamma)).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
    unfold isBot at 1.
    caseEq (project (G := BotValue) (beval V F m0 n gamma)).
    destruct b.
    apply (inject_i (subGF := Sub_SV_Bot_SV)); constructor; eauto.
    unfold isVI at 1.
    caseEq (project (G := NatValue) (beval V F n0 m gamma')).
    destruct n1.
    apply inject_project in H5; rename H5 into Eval_m'.
    destruct (SV_invertVI' _ SubV_m _ Eval_m') as [n_eq_vi | n_eq_bot];
      simpl in *|-.
    rewrite n_eq_vi in H2; unfold vi in H2;
      rewrite project_inject in H2; discriminate.
    rewrite n_eq_bot in H3; unfold bot in H3;
      rewrite project_inject in H3; discriminate.
    unfold isBot at 1.
    caseEq (project (G := BotValue) (beval V F n0 m gamma')).
    destruct b.
    apply inject_project in H6; rename H6 into Eval_m'.
    generalize (SV_invertBot _ SV _ SubV_m Eval_m').
    simpl; unfold bot, inject'; intros Eval_m.
    rewrite Eval_m, project_inject in H3; discriminate.
    unfold isBot at 1.
    caseEq (project (G := BotValue) (beval V F n0 n gamma')).
    destruct b.
    apply inject_project in H7; rename H7 into Eval_n'.
    generalize (SV_invertBot _ SV _ SubV_n Eval_n').
    simpl; unfold bot; intros Eval_n.
    rewrite Eval_n, project_inject in H4; discriminate.
    apply (inject_i (subGF := Sub_SV_refl_SV)); constructor; eauto.
  Qed.

  Lemma project_bot_bot : project (F := V) (G := BotValue) (bot _) = Some (Bot _).
  Proof.
    intros; unfold bot; rewrite project_inject; reflexivity.
  Qed.

  Global Instance Arith_eval_continuous_Exp :
    FPAlgebra (eval_continuous_Exp_P V F SV) (inject' Arith).
  Proof.
    constructor; unfold Algebra; intros.
    eapply ind_alg_Arith.
    apply eval_continuous_Exp_H.
    apply eval_continuous_Exp_H0.
  Defined.

  Context {eval_continuous_Exp_E : FPAlgebra (eval_continuous_Exp_P V F SV) (inject' F)}.

  (* ============================================== *)
  (* WELL-FORMED NAT VALUES                         *)
  (* ============================================== *)

  Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
  Context `{ispf_WFV : iSPF _ WFV}.

  (** Natrual Numbers are well-formed **)

  Inductive WFValue_VI (WFV : WFValue_i D V -> Prop) : WFValue_i D V -> Prop :=
  | WFV_VI : forall n,
    WFValue_VI WFV (mk_WFValue_i D V (vi n) tnat).

  Inductive WFV_VI_S : WFValue_i D V -> Set :=
    SWFV_VI : forall n,
    WFV_VI_S (mk_WFValue_i D V (vi n) tnat).

  Inductive WFV_VI_P : forall (i : WFValue_i D V), WFV_VI_S i -> Set :=.
  Definition WFV_VI_R (i : WFValue_i D V) (s : WFV_VI_S i) (p : WFV_VI_P i s) :
    WFValue_i D V := match p with end.

  Definition WFV_VI_to A i : IExt _ _ WFV_VI_R A i -> WFValue_VI A i :=
    fun x =>
      match x with
        | iext s pf =>
          match s with
            | SWFV_VI n => WFV_VI A n
          end
      end.

  Definition WFV_VI_from A i : WFValue_VI A i -> IExt _ _ WFV_VI_R A i :=
    fun x => match
      x in (WFValue_VI _ i) return (IExt _ _ WFV_VI_R A i)
    with
      | WFV_VI n =>
        iext _ _
             (SWFV_VI n)
             (fun p : WFV_VI_P _ _ =>
                match p with end)
    end.

  Global Instance WFV_VI_Container : IContainer WFValue_VI :=
    {| IS    := WFV_VI_S;
       IP    := WFV_VI_P;
       IR    := WFV_VI_R;
       ifrom := WFV_VI_from;
       ito   := WFV_VI_to
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl.
    f_equal; extensionality p; destruct p.
  Defined.

  Definition ind_alg_WFV_VI (P : WFValue_i D V -> Prop)
    (H : forall n, P (mk_WFValue_i _ _ (vi n) tnat))
    i (e : WFValue_VI P i) : P i :=
    match e in WFValue_VI _ i return P i with
      | WFV_VI n => H n
    end.

  Variable Sub_WFV_VI_WFV : Sub_iFunctor WFValue_VI WFV.

  (* Inversion principles for Well-formed natural numbers. *)
  Definition WF_invertVI_P (i : WFValue_i D V) :=
    wfv_b _ _ i = tnat ->
    WFValue_VI (iFix' WFV) i \/ (wfv_a D V i = bot V).

  Inductive WF_invertVI_Name := wfv_invertvi_name.
  Context {WF_invertVI_WFV :
    iPAlgebra WF_invertVI_Name WF_invertVI_P WFV}.

  Global Instance WF_invertVI_VI :
    iPAlgebra WF_invertVI_Name WF_invertVI_P WFValue_VI.
  Proof.
    constructor.
    unfold iAlgebra; intros; unfold WF_invertVI_P.
    inversion H; subst; simpl; intros.
    left; econstructor; auto.
  Defined.

  Global Instance WF_invertVI_Bot :
    iPAlgebra WF_invertVI_Name WF_invertVI_P (WFValue_Bot _ _).
    constructor.
  Proof.
    unfold iAlgebra; intros; unfold WF_invertVI_P.
    inversion H; subst; simpl; intros.
    right; reflexivity.
  Defined.

  Definition WF_invertVI := ifold_ (if_algebra (iPAlgebra := WF_invertVI_WFV)).

  Lemma Arith_eval_Soundness_H
    (typeof_R eval_R : Set) typeof_rec eval_rec
    {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
    {WF_eval_F' : WF_FAlgebra EvalName _ _ Arith F
       (MAlgebra_eval_Arith _) (eval_F')} :
    forall n : nat,
      forall gamma'' : Env (Names.Value V),
        forall T : Names.DType D,
          Arith_typeof typeof_R typeof_rec (Lit _ n) = Some T ->
          WFValueC D V WFV (Arith_eval eval_R eval_rec (Lit _ n) gamma'') T.
  Proof.
    intros n gamma'' T H4; intros.
    injection H4; intros; subst.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); constructor.
  Defined.

  Lemma Arith_eval_Soundness_H0
    (typeof_R eval_R : Set) typeof_rec eval_rec
    {eval_F' : FAlgebra EvalName eval_R (evalR V) F}
    {WF_eval_F' : WF_FAlgebra EvalName _ _ Arith F
       (MAlgebra_eval_Arith _) (eval_F')} :
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
  Proof.
    simpl; intros a b a' b' gamma'' IH_a IH_b T H4.
    caseEq (typeof_rec a); intros; rename H into typeof_a;
      unfold typeofR in typeof_a, H4; rewrite typeof_a in H4;
        try discriminate.
    caseEq (typeof_rec b); intros; rename H into typeof_b;
      unfold typeofR in typeof_b, H4; rewrite typeof_b in H4;
        try discriminate.
    caseEq (isTNat d); intros; rename H into d_eq; rewrite
      d_eq in H4; try discriminate.
    caseEq (isTNat d0); intros; rename H into d0_eq; rewrite
      d0_eq in H4; try discriminate.
    injection H4; intros; subst; clear H4.
    unfold isTNat in d_eq, d0_eq.
    caseEq (project d); intros; rewrite H in d_eq;
      try discriminate; clear d_eq; rename H into d_eq; destruct a0.
    caseEq (project d0); intros; rewrite H in d0_eq;
      try discriminate; clear d0_eq; rename H into d0_eq; destruct a0.
    apply inject_project in d_eq; apply inject_project in d0_eq.
    generalize (IH_a _ typeof_a) as WF_a;
    generalize (IH_b _ typeof_b) as WF_b; intros.
    destruct (WF_invertVI _ WF_a d_eq) as [beval_a' | beval_a'];
    destruct (WF_invertVI _ WF_b d0_eq) as [beval_b' | beval_b'];
    simpl in *; inversion beval_a'; inversion beval_b';
      repeat rewrite isVI_vi; repeat rewrite isVI_bot;
      repeat rewrite isBot_vi; repeat rewrite isBot_bot; subst.
    apply (inject_i (subGF := Sub_WFV_VI_WFV)); constructor.
    rewrite H2, isVI_bot, isBot_bot in *.
    assumption.
    rewrite H0, isVI_bot, isBot_bot in *.
    assumption.
    rewrite H0, isVI_bot, isBot_bot in *.
    assumption.
  Defined.

  Context {Typeof_F : forall T, FAlgebra TypeofName T (typeofR D) F}.
  Context {WF_typeof_F : forall T, WF_FAlgebra TypeofName T _ _ _
    (MAlgebra_typeof_Arith _) (Typeof_F _)}.
  Context {WF_Value_continous_alg :
    iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.

  Global Instance Arith_eval_Soundness_alg
    (P_bind : Set)
    (P : P_bind -> Env Value -> Prop)
    (E' : Set -> Set)
    `{spf_E' : SPF E'}
    {Sub_Arith_E' : Arith :<: E'}
    {WF_Fun_E' : WF_Functor _ _ Sub_Arith_E'}
    {Typeof_E' : forall T, FAlgebra TypeofName T (typeofR D) E'}
    {WF_typeof_E' : forall T, @WF_FAlgebra TypeofName T _ _ _
      Sub_Arith_E' (MAlgebra_typeof_Arith T) (Typeof_E' T)}
    (pb : P_bind)
    (eval_rec : Exp -> evalR V)
    (typeof_rec : Fix' E' -> typeofR D)
    :
    FPAlgebra (eval_alg_Soundness_P D V F WFV _ P
      _ pb typeof_rec eval_rec (f_algebra (FAlgebra := Typeof_E' _))
      (f_algebra (FAlgebra := eval_F))) (inject2 (F := Arith)).
  Proof.
    constructor.
      apply ind2_alg_Arith;
      unfold eval_alg_Soundness_P, inject2, inject; simpl; intros;
      rewrite out_in_inverse; rewrite out_in_inverse in H;
      rewrite (@wf_mixin _ _ _ _ _ _ _ WF_eval_F); simpl;
      rewrite (@wf_mixin _ _ _ _ _ _ _ (WF_typeof_E' _)) in H; simpl in H.
      (* Lit Case *)
      apply Arith_eval_Soundness_H with
        (typeof_R := Fix' E') (eval_R := Exp)
        (typeof_rec := typeof_rec) (eval_rec := eval_rec)
        (eval_F' := eval_F) (gamma'' := gamma''); auto.
      (* Add Case *)
      apply Arith_eval_Soundness_H0 with
        (typeof_R := Fix' E') (typeof_rec := typeof_rec)
        (eval_F' := eval_F) (a := fst m) (b := fst n); auto.
      apply (IHa _ _ WF_gamma'' m); simpl; auto;
        intros; apply (IHm _ WF_gamma'' IHa); auto.
      apply (IHa _ _ WF_gamma'' n); simpl; auto;
        intros; apply (IHn _ WF_gamma'' IHa); auto.
    Defined.

End Arith.

Hint Extern 1 (iPAlgebra SV_invertVI_Name (SV_invertVI_P _) _) =>
    constructor; unfold iAlgebra; unfold SV_invertVI_P; intros i H n H0;
      inversion H; subst; simpl in H0; revert H0;
        match goal with H : ?v = _ |- ?v = _ -> _ => rewrite H end; intros;
          discriminate_inject H0.

Hint Extern 1 (iPAlgebra SV_invertVI'_Name (SV_invertVI'_P _) _) =>
    constructor; unfold iAlgebra; unfold SV_invertVI'_P; intros i H n H0;
      inversion H; subst; simpl in H0; revert H0;
        match goal with H : ?v = _ |- ?v = _ -> _ => rewrite H end; intros;
          discriminate_inject H0.

Hint Extern 5 (iPAlgebra WF_invertVI_Name (WF_invertVI_P _ _ _) _) =>
  constructor; intros i H; unfold WF_invertVI_P;
    inversion H; subst; intro eq_H;
      discriminate_inject eq_H.

(*
Hint Extern 0 =>
  intros; match goal with
            |- (PAlgebra eval_Soundness_alg_Name
              (sig (UP'_P2 (eval_alg_Soundness_P _ _ _ _ _ _ _ _ _ _ _ _ _ _))) Arith) =>
            eapply Arith_eval_Soundness_alg; eauto with typeclass_instances
          end : typeclass_instances.
*)
