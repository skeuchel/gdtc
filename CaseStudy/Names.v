Require Import List.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.

Section Names.

  (* ============================================== *)
  (* ENVIRONMENTS                                   *)
  (* ============================================== *)

  Definition Env (A : Set) := list A.

  Fixpoint lookup {A: Set} (As : Env A) (i : nat) : option A :=
    match As, i with
      | nil, _  => None
      | cons _ As', S i' => lookup As' i'
      | cons a _, 0 => Some a
    end.

  Fixpoint insert (A : Set) (e : A) (env : Env A) : Env A :=
    match env in list _ return Env A with
      | nil => cons e (nil)
      | cons e' env' => cons e' (@insert _ e env')
    end.

  Definition empty A : Env A := nil.


  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)


  (** SuperFunctor for Types. **)
  Variable DT : Set -> Set.
  Context {fun_DT : Functor DT}.
  Context {pfun_DT : PFunctor DT}.
  Context {spf_DT : SPF DT}.
  Definition DType := Fix DT.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)


  (** SuperFunctor for Values. **)

  Variable V : Set -> Set.
  Context {Fun_V : Functor V}.
  Context {PFun_V : PFunctor V}.
  Context {spf_V : SPF V}.
  Definition Value := Fix V.

  (** ERROR VALUES **)

   Inductive StuckValue (A : Set) : Set :=
    | Stuck : nat -> StuckValue A.

   Context {Sub_StuckValue_V : StuckValue :<: V}.

  Global Instance StuckValue_Container : Container StuckValue.
    apply (ConstContainer nat StuckValue
            (fun A x => match x with Stuck n => n end)
            Stuck).
    intros; reflexivity.
    destruct x; reflexivity.
  Defined.

  Definition stuck (n : nat) : Value := inject StuckValue V (Stuck _ n).

  (* Induction Principle for Stuckor Values. *)

  Definition ind_alg_Stuck (P : Value -> Prop) (H : forall n, P (stuck n)) :
    PAlgebra (inject StuckValue V) P := fun xs Axs =>
    match xs return P (inject StuckValue V xs) with
      | Stuck n => H n
    end.

  Definition ind_palg_Stuck (P : Value -> Prop)
             (H : forall n, P (stuck n)) :
    FPAlgebra P (inject StuckValue V) :=
    {| p_algebra := ind_alg_Stuck P H |}.

  (** BOTTOM VALUES **)

  Inductive BotValue (A : Set) : Set :=
  | Bot : BotValue A.

  Global Instance BotValue_Container : Container BotValue.
    apply (ConstContainer unit BotValue
            (fun A x => match x with Bot => tt end)
            (fun A x => Bot _)).
    destruct x; reflexivity.
    destruct x; reflexivity.
  Defined.

  Context {Sub_BotValue_V : BotValue :<: V}.

  (* Constructor + Universal Property. *)
  Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V}.

  Definition bot : Value := inject BotValue V (Bot _).
  Hint Unfold bot.

  Definition ind_alg_Bot (P : Value -> Prop) (H : P bot) :
    PAlgebra (inject BotValue V) P :=
    fun xs Axs =>
      match xs return P (inject BotValue V xs) with
        | Bot => H
      end.

  (* Constructor Testing for Bottom Values. *)

  Definition isBot : Value -> bool :=
    fun exp =>
      match project BotValue V exp with
       | Some Bot  => true
       | None      => false
      end.

  Lemma isBot_bot : isBot bot = true.
  Proof.
    unfold isBot, bot.
    now rewrite project_inject.
  Qed.


  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set.
  Context {Fun_E : Functor E}.
  Context {PFun_E : PFunctor E}.
  Context {spf_E : SPF E}.
  Definition Exp := Fix E.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)


  (** TYPING **)

  Definition typeofR  := option DType.
  Inductive TypeofName : Set := typeofname.
  Context {Typeof_E : forall T,
    FAlgebra TypeofName T typeofR E}.
  Definition typeof := fold_ (f_algebra TypeofName id).

  (** EVALUATION **)

  Definition evalR : Set := Env Value -> Value.

  Inductive EvalName := evalname.

  Context {eval_E : forall T, FAlgebra EvalName T evalR E}.
  Definition eval := fold_ (f_algebra EvalName id).

  Context {beval_E : FAlgebra EvalName Exp evalR E}.

  Definition beval (n: nat) :=
    boundedFix n (@f_algebra _ _ _ _ beval_E) (fun _ => bot).

  (** DTYPE EQUALITY **)

  Context {Eq_DType : Eq DType}.
  Definition eq_DType : DType -> DType -> bool := eq.

  Definition eq_DType_eq_P (d : DType) := forall d2,
    eq_DType d d2 = true -> d = d2.
  Lemma eq_DType_eq : forall (d1 : DType), eq_DType_eq_P d1.
  Proof.
   unfold eq_DType_eq_P.
   apply eq_propositional_true.
  Qed.

  (** PRETTY PRINTING **)

  Require Import String.
  Require Import Ascii.

  Definition DTypePrintR := string.
  Inductive DTypePrintName := dtypeprintname.
  Context {DTypePrint_DT : forall T, FAlgebra DTypePrintName T DTypePrintR DT}.
  Definition DTypePrint := fold_ (f_algebra DTypePrintName id).

  Definition ExpPrintR := nat -> string.
  Inductive ExpPrintName := expprintname.
  Context {ExpPrint_E : forall T, FAlgebra ExpPrintName T ExpPrintR E}.
  Definition ExpPrint := fold_ (f_algebra ExpPrintName id).

  Definition ValuePrintR := string.
  Inductive ValuePrintName := valueprintname.
  Context {ValuePrint_V : forall T, FAlgebra ValuePrintName T ValuePrintR V}.
  Definition ValuePrint := fold_ (f_algebra ValuePrintName id).

  (* Printers for Bot and Stuck *)
   Global Instance MAlgebra_ValuePrint_BotValue T : FAlgebra ValuePrintName T ValuePrintR BotValue :=
     {| f_algebra :=  fun _ _ => append "bot" "" |}.

   Global Instance MAlgebra_ValuePrint_StuckValue T : FAlgebra ValuePrintName T ValuePrintR StuckValue :=
     {| f_algebra :=
       fun _ e => match e with
                      | Stuck n => append "Stuck " (String (ascii_of_nat (n + 48)) EmptyString)
                    end|}.

  (* ============================================== *)
  (* PREDICATE LIFTERS FOR LISTS                    *)
  (* ============================================== *)

    (* Unary Predicates.*)
    Inductive P_Env {A : Set} (P : A -> Prop) : forall (env : Env A), Prop :=
    | P_Nil : P_Env P nil
    | P_Cons : forall a (As : Env _), P a -> P_Env P As ->
      P_Env P (cons a As).

    Lemma P_Env_lookup : forall A (env : Env A) P,
      P_Env P env ->
      forall n v,
        lookup env n = Some v -> P v.
      intros A env P P_env; induction P_env;
        destruct n; simpl; intros; try discriminate.
      injection H0; intros; subst; eauto.
      eauto.
    Qed.

    Lemma P_Env_Lookup : forall A (env : Env A) (P : A -> Prop),
      (forall n v,
        lookup env n = Some v -> P v) ->
      P_Env P env.
      intros A env P H; induction env; constructor.
      eapply (H 0); eauto.
      apply IHenv; intros; eapply (H (S n)); eauto.
    Qed.

    Lemma P_Env_insert : forall A (env : Env A) (P : A -> Prop),
      P_Env P env -> forall a, P a -> P_Env P (insert _ a env).
      induction env; simpl; intros; constructor; eauto.
      inversion H; subst; eauto.
      eapply IHenv; inversion H; eauto.
    Qed.

    (* Binary Predicates.*)
    Inductive P2_Env {A B : Set} (P : A -> B -> Prop) : forall (env : Env A) (env : Env B), Prop :=
    | P2_Nil : P2_Env P nil nil
    | P2_Cons : forall a b (As : Env _) (Bs : Env _), P a b -> P2_Env P As Bs ->
      P2_Env P (cons a As) (cons b Bs).

    Inductive P2_Shape {A B : Set} : Env A -> Env B -> Prop :=
    | P2S_Nil : P2_Shape nil nil
    | P2S_Cons : forall a b {As : Env _} {Bs : Env _}, P2_Shape As Bs ->
      P2_Shape (cons a As) (cons b Bs).

    Fixpoint P2_Shape_irrelevance {A B : Set} {As : Env A} {Bs : Env B}
             (s : P2_Shape As Bs) : forall s', s = s'.
    Proof.
      destruct s.
      intros s'.
      dependent destruction s'.
      reflexivity.
      intros s'.
      dependent destruction s'.
      rewrite (P2_Shape_irrelevance A B As Bs s s').
      reflexivity.
    Defined.

    Definition P2_Env_Shape {A B : Set} {P : A -> B -> Prop} {As : Env A} {Bs : Env B} :
      P2_Env P As Bs -> P2_Shape As Bs.
    Proof.
      intros ps; induction ps; constructor; auto.
    Defined.

    Inductive P2_Index {A B : Set} (a : A) (b : B) :
      forall {As : Env A} {Bs : Env B}, P2_Shape As Bs -> Set :=
    | P2I_Here  : forall {As Bs} (s : P2_Shape As Bs),
                    P2_Index a b (P2S_Cons a b s)
    | P2I_There : forall a' b' {As Bs} (s : P2_Shape As Bs),
                    P2_Index a b s ->
                    P2_Index a b (P2S_Cons a' b' s).

    Fixpoint P2_tabulate {A B : Set} {P : A -> B -> Prop}
      {As : Env A} {Bs : Env B} (s : P2_Shape As Bs) :
      (forall (a : A) (b : B), P2_Index a b s -> P a b) -> P2_Env P As Bs :=
      match s in (P2_Shape As Bs) return
        ((forall a b, P2_Index a b s -> P a b) -> P2_Env P As Bs)
      with
        | P2S_Nil => fun _ => P2_Nil P
        | P2S_Cons _ _ _ _ s =>
          fun pf =>
            P2_Cons _ _ _ _ _
              (pf _ _ (P2I_Here _ _ s))
              (P2_tabulate _
                 (fun _ _ i => pf _ _ (P2I_There _ _ _ _ s i)))
      end.

    Fixpoint P2_lookup {A B : Set} {P : A -> B -> Prop}
      {As : Env A} {Bs : Env B} (s : P2_Shape As Bs) (ps : P2_Env P As Bs) :
      forall (a : A) (b : B), P2_Index a b s -> P a b.
    Proof.
      intros a b idx.
      destruct idx.
      inversion ps.
      apply H2.
      inversion ps.
      apply (P2_lookup _ _ _ _ _ _ H4 _ _ idx).
    Defined.

    Fixpoint P2_tabulate_lookup' {A B : Set} {P : A -> B -> Prop}
             {As : Env A} {Bs : Env B}
             (ps : P2_Env P As Bs) :
      P2_tabulate (P2_Env_Shape ps) (P2_lookup (P2_Env_Shape ps) ps) = ps.
    Proof.
      destruct ps; simpl.
      reflexivity.
      simpl.
      f_equal.
      apply (P2_tabulate_lookup' A B P As Bs ps).
    Qed.

    Lemma P2_tabulate_lookup {A B : Set} {P : A -> B -> Prop}
             {As : Env A} {Bs : Env B}
             (ps : P2_Env P As Bs)
    : forall s, P2_tabulate s (P2_lookup s ps) = ps.
    Proof.
      intro s.
      rewrite (P2_Shape_irrelevance s (P2_Env_Shape ps)).
      apply P2_tabulate_lookup'.
    Qed.

    Lemma P2_lookup_tabulate {A B : Set} (P : A -> B -> Prop)
             {As : Env A} {Bs : Env B} (s : P2_Shape As Bs)
             (f : forall (a : A) (b : B), P2_Index a b s -> P a b)
             (a : A) (b : B) (i : P2_Index a b s)
    : P2_lookup s (P2_tabulate s f) _ _ i = f _ _ i.
    Proof.
      induction i; simpl.
      reflexivity.
      rewrite IHi.
      reflexivity.
    Qed.

    Lemma P2_Env_lookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n v,
        lookup env n = Some v -> exists v', lookup env' n = Some v' /\
          P v v'.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      exists b; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.

    Lemma P2_Env_lookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n v,
        lookup env' n = Some v -> exists v', lookup env n = Some v' /\
          P v' v.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate.
      eexists; injection H0; intros; subst; split; eauto.
      eauto.
    Qed.

    Lemma P2_Env_Nlookup : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n,
        lookup env n = None -> lookup env' n = None.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate; auto.
    Qed.

    Lemma P2_Env_Nlookup' : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' ->
      forall n,
        lookup env' n = None -> lookup env n = None.
      intros A B env env' P P_env_env'; induction P_env_env';
        destruct n; simpl; intros; try discriminate; auto.
    Qed.

    Lemma P2_Env_length : forall A B (env : Env A) (env' : Env B) P,
      P2_Env P env env' -> List.length env = List.length env'.
      intros; induction H; simpl; congruence.
    Qed.

    Lemma P2_Env_insert : forall A B (env : Env A) (env' : Env B) (P : A -> B -> Prop),
      P2_Env P env env' ->
      forall a b, P a b -> P2_Env P (insert _ a env) (insert _ b env').
      intros; induction H; simpl; constructor; eauto.
      constructor.
    Qed.

    (* Need this better induction principle when we're reasoning about
       Functors that use P2_Envs. *)
    Definition P2_Env_ind' :=
    fun (A B : Set) (P : A -> B -> Prop) (P0 : forall As Bs, P2_Env P As Bs -> Prop)
      (f : P0 _ _ (P2_Nil _))
      (f0 : forall (a : A) (b : B) (As : Env A) (Bs : Env B) (ABs : P2_Env P As Bs)
        (P_a_b : P a b), P0 _ _ ABs -> P0 _ _ (P2_Cons P a b As Bs P_a_b ABs)) =>
        fix F (env : Env A) (env0 : Env B) (p : P2_Env P env env0) {struct p} :
        P0 env env0 p :=
        match p in (P2_Env _ env1 env2) return (P0 env1 env2 p) with
        | P2_Nil => f
        | P2_Cons a b As Bs y p0 => f0 a b As Bs p0 y (F As Bs p0)
      end.

  (* ============================================== *)
  (* SUBVALUE RELATION                              *)
  (* ============================================== *)


    Record SubValue_i : Set := mk_SubValue_i
      {sv_a : Value;
        sv_b : Value}.

    (** SuperFunctor for SubValue Relation. **)

    Variable SV : (SubValue_i -> Prop) -> SubValue_i -> Prop.
    Context `{ispf_SV : iSPF _ SV}.
    Definition SubValue := iFix SV.
    Definition SubValueC V1 V2:= SubValue (mk_SubValue_i V1 V2).

    (** Subvalue is reflexive **)
    Inductive SubValue_refl (A : SubValue_i -> Prop) : SubValue_i -> Prop :=
      SV_refl : forall v v',
        v = v' ->
        SubValue_refl A (mk_SubValue_i v v').

    Inductive SV_refl_S : SubValue_i -> Set :=
      SSV_refl : forall v (v' : Value), v = v' -> SV_refl_S (mk_SubValue_i v v').
    Inductive SV_refl_P : forall (i : SubValue_i), SV_refl_S i -> Set :=.
    Definition SV_refl_R (i : SubValue_i) (s : SV_refl_S i) (p : SV_refl_P i s) :
      SubValue_i := match p with end.

    Definition SV_refl_to A i : IExt _ _ SV_refl_R A i -> SubValue_refl A i :=
      fun x =>
        match x with
          | iext s pf =>
            match s with
              | SSV_refl v v' e => SV_refl A v v' e
            end
        end.

    Definition SV_refl_from A i : SubValue_refl A i -> IExt _ _ SV_refl_R A i :=
      fun x => match
        x in (SubValue_refl _ i) return (IExt SV_refl_S SV_refl_P SV_refl_R A i)
      with
        | SV_refl v v' e =>
          iext _ _
               (SSV_refl v v' e)
               (fun p : SV_refl_P _ _ =>
                  match p with end)
      end.


    Global Instance SV_refl_Container : IContainer SubValue_refl :=
      {| IS    := SV_refl_S;
         IP    := SV_refl_P;
         IR    := SV_refl_R;
         ifrom := SV_refl_from;
         ito   := SV_refl_to
      |}.
    Proof.
      intros; destruct a; reflexivity.
      intros; destruct a; destruct s; simpl.
      f_equal; extensionality p; destruct p.
    Defined.

    Definition ind_alg_SV_refl (P : SubValue_i -> Prop)
      (H : forall v v', v = v' -> P (mk_SubValue_i v v'))
      i (e : SubValue_refl P i) : P i :=
      match e in SubValue_refl _ i return P i with
        | SV_refl v v' eq_v => H v v' eq_v
      end.

  Variable Sub_SV_refl_SV : Sub_iFunctor SubValue_refl SV.

  (** Bot is Bottom element for this relation **)
  Inductive SubValue_Bot (A : SubValue_i -> Prop) : SubValue_i -> Prop :=
    SV_Bot : forall v v', v = inject BotValue V (Bot _) ->
      SubValue_Bot A (mk_SubValue_i v v').

  Inductive SV_Bot_S : SubValue_i -> Set :=
    SSV_Bot : forall v (v' : Value), v = inject BotValue V (Bot _) ->
      SV_Bot_S (mk_SubValue_i v v').
  Inductive SV_Bot_P : forall (i : SubValue_i), SV_Bot_S i -> Set :=.
  Definition SV_Bot_R (i : SubValue_i) (s : SV_Bot_S i) (p : SV_Bot_P i s) :
    SubValue_i := match p with end.

  Definition SV_Bot_to A i : IExt _ _ SV_Bot_R A i -> SubValue_Bot A i :=
    fun x =>
      match x with
        | iext s pf =>
          match s with
            | SSV_Bot v v' e => SV_Bot A v v' e
          end
      end.

  Definition SV_Bot_from A i : SubValue_Bot A i -> IExt _ _ SV_Bot_R A i :=
    fun x => match
      x in (SubValue_Bot _ i) return (IExt SV_Bot_S SV_Bot_P SV_Bot_R A i)
    with
      | SV_Bot v v' e =>
        iext _ _
             (SSV_Bot v v' e)
             (fun p : SV_Bot_P _ _ =>
                match p with end)
    end.

  Global Instance SV_Bot_Container : IContainer SubValue_Bot :=
    {| IS    := SV_Bot_S;
       IP    := SV_Bot_P;
       IR    := SV_Bot_R;
       ifrom := SV_Bot_from;
       ito   := SV_Bot_to
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl.
    f_equal; extensionality p; destruct p.
  Defined.

  Definition ind_alg_SV_Bot (P : SubValue_i -> Prop)
    (H : forall v v', v = inject BotValue V (Bot _) -> P (mk_SubValue_i v v'))
    i (e : SubValue_Bot P i) : P i :=
    match e in SubValue_Bot _ i return P i with
      | SV_Bot v v' eq_v => H v v' eq_v
    end.

  Variable Sub_SV_Bot_SV : Sub_iFunctor SubValue_Bot SV.

  (* Inversion principle for Bottom SubValues. *)
  Definition SV_invertBot_P (i : SubValue_i) :=
    sv_b i = bot -> sv_a i = bot.

  Inductive SV_invertBot_Name := ece_invertbot_name.
  Context {SV_invertBot_SV :
    iPAlgebra SV_invertBot_Name SV_invertBot_P SV}.

  Global Instance SV_invertBot_refl :
    iPAlgebra SV_invertBot_Name SV_invertBot_P (SubValue_refl).
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertBot_P.
    inversion H; subst; simpl; congruence.
  Defined.

  Global Instance SV_invertBot_Bot :
    iPAlgebra SV_invertBot_Name SV_invertBot_P SubValue_Bot.
    econstructor; intros.
    unfold iAlgebra; intros; unfold SV_invertBot_P.
    inversion H; subst; simpl; eauto.
  Defined.

  Definition SV_invertBot := ifold_ (if_algebra (iPAlgebra := SV_invertBot_SV)).
  (* End Inversion principle for SubValue.*)

  (** SubValue lifted to Environments **)
  Definition Sub_Environment (env env' : Env _) :=
    P2_Env SubValueC env env'.

  Lemma Sub_Environment_refl : forall (env : Env _),
    Sub_Environment env env.
    induction env; econstructor; eauto.
    apply (inject_i (subGF := Sub_SV_refl_SV));
      constructor; reflexivity.
  Qed.

  (* ============================================== *)
  (* EVALUATION IS CONTINUOUS                        *)
  (* ============================================== *)

    (** Helper property for proof of continuity of evaluation. **)
    Definition eval_continuous_Exp_P (e : Exp) :=
      forall (m : nat),
        (forall (e0 : Exp)
          (gamma gamma' : Env Value) (n : nat),
          Sub_Environment gamma gamma' ->
          m <= n -> SubValueC (beval m e0 gamma) (beval n e0 gamma')) ->
        forall (gamma gamma' : Env Value) (n : nat),
          Sub_Environment gamma gamma' ->
          m <= n ->
          SubValueC (beval (S m) e gamma) (beval (S n) e gamma').

    Inductive EC_ExpName := ec_expname.

    Context {eval_continuous_Exp_E :
      FPAlgebra (eval_continuous_Exp_P) (inject E E)}.

    (** Evaluation is continuous. **)
    Lemma beval_continuous : forall m,
      forall (e : Exp) (gamma gamma' : Env _),
        forall n (Sub_G_G' : Sub_Environment gamma gamma'),
          m <= n ->
          SubValueC (beval m e gamma) (beval n e gamma').
      induction m; simpl.
      intros; eapply in_ti; eapply inj_i; econstructor; simpl; eauto.
      intros; destruct n; try (inversion H; fail).
      assert (m <= n) as le_m_n0 by auto with arith; clear H.
      revert m IHm gamma gamma' n Sub_G_G' le_m_n0.
      fold (eval_continuous_Exp_P e).
      apply Ind.
    Qed.

  (* ============================================== *)
  (* WELL-FORMED VALUES RELATION                     *)
  (* ============================================== *)

    Record WFValue_i : Set := mk_WFValue_i
      {wfv_a : Value;
        wfv_b : DType}.

    (** SuperFunctor for Well-Formed Value Relation. **)

    Variable WFV : (WFValue_i -> Prop) -> WFValue_i -> Prop.
    Context `{ispf_WFV : iSPF _ WFV}.
    Definition WFValue := iFix WFV.
    Definition WFValueC V T:= WFValue (mk_WFValue_i V T).

    (** Bottom is well-formed **)

    Inductive WFValue_Bot (A : WFValue_i -> Prop) : WFValue_i -> Prop :=
      WFV_Bot : forall v T,
        v = inject BotValue V (Bot _) ->
        WFValue_Bot A (mk_WFValue_i v T).

    Inductive WFV_Bot_S : WFValue_i -> Set :=
      SWFV_Bot : forall v T,
      v = bot ->
      WFV_Bot_S (mk_WFValue_i v T).

    Inductive WFV_Bot_P : forall (i : WFValue_i), WFV_Bot_S i -> Set :=.
    Definition WFV_Bot_R (i : WFValue_i) (s : WFV_Bot_S i) (p : WFV_Bot_P i s) :
      WFValue_i := match p with end.

    Definition WFV_Bot_to A i : IExt _ _ WFV_Bot_R A i -> WFValue_Bot A i :=
      fun x =>
        match x with
          | iext s pf =>
            match s with
              | SWFV_Bot v T eq => WFV_Bot A v T eq
            end
        end.

    Definition WFV_Bot_from A i : WFValue_Bot A i -> IExt _ _ WFV_Bot_R A i :=
      fun x => match
        x in (WFValue_Bot _ i) return (IExt _ _ WFV_Bot_R A i)
      with
        | WFV_Bot v T eq =>
          iext _ _
               (SWFV_Bot v T eq)
               (fun p : WFV_Bot_P _ _ =>
                  match p with end)
      end.

    Global Instance WFV_Bot_Container : IContainer WFValue_Bot :=
      {| IS    := WFV_Bot_S;
         IP    := WFV_Bot_P;
         IR    := WFV_Bot_R;
         ifrom := WFV_Bot_from;
         ito   := WFV_Bot_to
      |}.
    Proof.
      intros; destruct a; reflexivity.
      intros; destruct a; destruct s; simpl.
      f_equal; extensionality p; destruct p.
    Defined.

    Variable WF_WFV_Bot_WFV : Sub_iFunctor WFValue_Bot WFV.

    Definition WF_Environment env env' :=
      P2_Env (fun v T =>
        match T with
          | Some T => WFValueC v T
          | None => False
        end) env env'.

  (* ============================================== *)
  (* Evaluation preserves Well-Formedness           *)
  (* ============================================== *)

    Definition WF_Value_continuous_P i :=
      forall T, WFValueC (sv_b i) T -> WFValueC (sv_a i) T.

    Inductive WFV_ContinuousName : Set := wfv_continuousname.

    Context {WF_Value_continous_alg : iPAlgebra WFV_ContinuousName WF_Value_continuous_P SV}.

    Global Instance WFV_Value_continuous_refl  :
      iPAlgebra WFV_ContinuousName WF_Value_continuous_P SubValue_refl.
      constructor; unfold iAlgebra; intros.
      inversion H; subst.
      unfold WF_Value_continuous_P. auto.
    Qed.

    Global Instance WFV_Value_continuous_Bot  :
      iPAlgebra WFV_ContinuousName WF_Value_continuous_P SubValue_Bot.
      constructor; unfold iAlgebra; intros.
      inversion H; subst.
      unfold WF_Value_continuous_P; simpl; intros.
      apply inject_i; constructor; auto.
    Qed.

    Lemma WF_Value_continous : forall v v',
      SubValueC v v' ->
      WF_Value_continuous_P (mk_SubValue_i v v').
      intros; apply (ifold_ ); try assumption.
      apply if_algebra.
    Qed.

    Lemma WF_Value_beval : forall m n,
      forall (e : Exp) gamma gamma' T
        (Sub_G_G' : Sub_Environment gamma' gamma),
        m <= n ->
        WFValueC (beval n e gamma) T ->
        WFValueC (beval m e gamma') T.
      intros; eapply WF_Value_continous.
      eapply beval_continuous; try eassumption.
      eassumption.
    Qed.

    Variable (WF_MAlg_typeof : WF_MAlgebra Typeof_E).
    Variable (WF_MAlg_eval : WF_MAlgebra eval_E).

    Definition eval_alg_Soundness_P
      (P_bind : Set)
      (P : P_bind -> Env Value -> Prop)
      (E' : Set -> Set)
      `{spf_E' : SPF E'}
      (pb : P_bind)
      (typeof_rec : Fix E' -> typeofR)
      (eval_rec : Exp -> evalR)
      (typeof_F : Mixin (Fix E') E' typeofR)
      (eval_F : Mixin Exp E evalR)
      (e : (Fix E') * (Fix E)) :=
      forall
      gamma'' (WF_gamma'' : P pb gamma'')
      (IHa : forall pb gamma'' (WF_gamma'' : P pb gamma'') (a : (Fix E' * Exp)),
          (forall T,
            typeof_F typeof_rec (out_t (fst a)) = Some T ->
            WFValueC (eval_F eval_rec (out_t (snd a)) gamma'') T) ->
          forall T, typeof_rec (fst a) = Some T ->
            WFValueC (eval_rec (snd a) gamma'') T),
        forall T : DType,
          typeof_F typeof_rec (out_t (fst e)) = Some T ->
          WFValueC (eval_F eval_rec (out_t (snd e)) gamma'') T.

    Context {eval_Soundness_alg_F : forall typeof_rec eval_rec,
      FPAlgebra (eval_alg_Soundness_P unit (fun _ _ => True) _ tt
        typeof_rec eval_rec
        (f_algebra TypeofName (FAlgebra := Typeof_E _))
        (f_algebra EvalName (FAlgebra := eval_E _))) (inject2 E E E)}.

    Lemma eval_Soundness : forall (e : Exp),
      forall gamma'' T, typeof e = Some T ->
        WFValueC (eval e gamma'') T.
      intros.
      rewrite <- (@in_out_inverse _ _ _ _ e).
      unfold eval; rewrite fold_computation; fold eval.
      rewrite wf_malgebra.
      unfold id.
      try rewrite <- eta_expansion.
      apply (Ind2 (Ind_Alg := eval_Soundness_alg_F typeof eval)); auto.
      destruct a; simpl.
      intros.
      rewrite <- (@in_out_inverse _ _ _ _ e0).
      unfold eval; rewrite fold_computation; fold eval.
      rewrite wf_malgebra.
      unfold id.
      try rewrite <- eta_expansion.
      apply H0.
      unfold typeof in H1.
      rewrite <- (@in_out_inverse _ _ _ _ f) in H1.
      rewrite fold_computation in H1.
      rewrite wf_malgebra in H1.
      unfold id in H1.
      try rewrite <- eta_expansion in H1.
      apply H1.
      simpl.
      unfold typeof in H.
      rewrite <- (@in_out_inverse _ _ _ _ e) in H.
      rewrite fold_computation in H.
      rewrite wf_malgebra in H.
      unfold id in H.
      try rewrite <- eta_expansion in H.
      apply H.
    Qed.

End Names.

Ltac fold_beval :=
  repeat
    match goal with
      | [ |- context [ boundedFix ?m _ _ _ _ ] ] =>
        fold (beval _ _ m)
    end.

Ltac simpl_beval :=
  unfold beval; simpl;
  rewrite out_in_inverse;
  match goal with
    | [ WF_eval_F : WF_FAlgebra EvalName _ _ _ _ _ _ |- _ ] =>
      repeat rewrite (wf_mixin (WF_Mixin := WF_eval_F)); simpl
  end; fold_beval.
