Require Import FJ_tactics.
Require Import Containers.
Require Import Functors.
Require Import List.
Require Import Names.
Require Import FunctionalExtensionality.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Section PNames.

  (* ============================================== *)
  (* TYPES                                          *)
  (* ============================================== *)

  (** SuperFunctor for Types. **)
  Variable D : Set -> Set.
  Context `{spf_D : SPF D}.

  (* ============================================== *)
  (* VALUES                                         *)
  (* ============================================== *)

  (** SuperFunctor for Values. **)
  Variable V : Set -> Set.
  Context `{spf_V : SPF V}.

  Context {Sub_StuckValue_V : StuckValue :<: V}.
  Context {WF_SubStuckValue_V : WF_Functor _ _ Sub_StuckValue_V}.
  Context {Sub_BotValue_V : BotValue :<: V}.
  Context {WF_SubBotValue_V : WF_Functor _ _ Sub_BotValue_V}.

  (* ============================================== *)
  (* EXPRESSIONS                                    *)
  (* ============================================== *)

  (** SuperFunctor for Expressions. **)
  Variable E : Set -> Set -> Set.
  Context {fun_E : forall A, Functor (E A)}.
  Context {pfun_E: forall A, PFunctor (E A)}.
  Context {spf_E : forall A, SPF (E A)}.

  (* ============================================== *)
  (* OPERATIONS                                     *)
  (* ============================================== *)

  (** TYPING **)

  Context {Typeof_E : forall T,
    FAlgebra TypeofName T (typeofR D) (E (typeofR D))}.

  Context {eval_E : forall T, FAlgebra EvalName T (evalR V) (E nat)}.
  Context {beval_E : FAlgebra EvalName (Exp (E nat)) (evalR V) (E nat)}.

  (* ============================================== *)
  (* EXPRESSION EQUIVALENCE RELATION                *)
  (* ============================================== *)

  Section eqv_Section.

    Record eqv_i (A B : Set) : Set := mk_eqv_i
      {env_A : Env A;
        env_B : Env B;
        eqv_a : Fix' (E A);
        eqv_b : Fix' (E B)}.

    (** SuperFunctor for Equivalence Relation. **)
    Variable EQV_E : forall A B,
      (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.
    Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
    Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.

    Definition E_eqv A B := iFix' (EQV_E A B).
    Definition E_eqvC {A B : Set} gamma gamma' e e' :=
      E_eqv _ _ (mk_eqv_i A B gamma gamma' e e').

    Variable (NP : Set -> Set).
    Context `{spf_NP : SPF NP}.
    Context {sub_NP_F : forall A, NP :<: E A}.

    Inductive NP_Functor_eqv
      (A B : Set)
      (C : eqv_i A B -> Prop)
      : eqv_i A B -> Prop :=
    | NP_eqv_0 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, NP D)
      (np_all : forall (D : Set) (P : D -> Prop),
                  All P (np D)),
      e = inject (subGF := sub_NP_F A) (np _) ->
      e' = inject (subGF := sub_NP_F B) (np _) ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C'),
        fmap f (np A') = fmap g (np B')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_1 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d : D),
                  P d -> All P (np _ d))
      a a',
      e = inject (subGF := sub_NP_F A) (np _ a) ->
      e' = inject (subGF := sub_NP_F B) (np _ a') ->
      C (mk_eqv_i _ _ gamma gamma' a a') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' : A') (b' : B'), f a' = g b' ->
        fmap f (np A' a') = fmap g (np B' b')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_2 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d1 d2 : D),
                  P d1 -> P d2 -> All P (np _ d1 d2))
      a a' b b',
      e = inject (subGF := sub_NP_F A) (np _ a b) ->
      e' = inject (subGF := sub_NP_F B) (np _ a' b') ->
      C (mk_eqv_i _ _ gamma gamma' a a') ->
      C (mk_eqv_i _ _ gamma gamma' b b') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' : A') (b' b'' : B'), f a' = g b' -> f a'' = g b'' ->
        fmap f (np A' a' a'') = fmap g (np B' b' b'')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e')
    | NP_eqv_3 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d1 d2 d3 : D),
                  P d1 -> P d2 -> P d3 -> All P (np _ d1 d2 d3))
      a a' b b' c c',
      e = inject (subGF := sub_NP_F A) (np _ a b c) ->
      e' = inject (subGF := sub_NP_F B) (np _ a' b' c') ->
      C (mk_eqv_i _ _ gamma gamma' a a') ->
      C (mk_eqv_i _ _ gamma gamma' b b') ->
      C (mk_eqv_i _ _ gamma gamma' c c') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' a''' : A') (b' b'' b''' : B'),
        f a' = g b' -> f a'' = g b'' -> f a''' = g b''' ->
        fmap f (np A' a' a'' a''') = fmap g (np B' b' b'' b''')) ->
      NP_Functor_eqv A B C (mk_eqv_i _ _ gamma gamma' e e').

    Inductive NP_Functor_eqv_S
      (A B : Set)
      : eqv_i A B -> Type :=
    | SNP_eqv_0 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, NP D)
      (np_all : forall (D : Set) (P : D -> Prop),
                  All P (np D)),
      e = inject (subGF := sub_NP_F A) (np _) ->
      e' = inject (subGF := sub_NP_F B) (np _) ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C'),
        fmap f (np A') = fmap g (np B')) ->
      NP_Functor_eqv_S A B (mk_eqv_i _ _ gamma gamma' e e')
    | SNP_eqv_1 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d : D),
                  P d -> All P (np _ d))
      a a',
      e = inject (subGF := sub_NP_F A) (np _ a) ->
      e' = inject (subGF := sub_NP_F B) (np _ a') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' : A') (b' : B'), f a' = g b' ->
        fmap f (np A' a') = fmap g (np B' b')) ->
      NP_Functor_eqv_S A B (mk_eqv_i _ _ gamma gamma' e e')
    | SNP_eqv_2 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d1 d2 : D),
                  P d1 -> P d2 -> All P (np _ d1 d2))
      a a' b b',
      e = inject (subGF := sub_NP_F A) (np _ a b) ->
      e' = inject (subGF := sub_NP_F B) (np _ a' b') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' : A') (b' b'' : B'), f a' = g b' -> f a'' = g b'' ->
        fmap f (np A' a' a'') = fmap g (np B' b' b'')) ->
      NP_Functor_eqv_S A B (mk_eqv_i _ _ gamma gamma' e e')
    | SNP_eqv_3 : forall (gamma : Env A) (gamma' : Env B)
      e e' (np : forall D : Set, D -> D -> D -> NP D)
      (np_all : forall (D : Set) (P : D -> Prop) (d1 d2 d3 : D),
                  P d1 -> P d2 -> P d3 -> All P (np _ d1 d2 d3))
      a a' b b' c c',
      e = inject (subGF := sub_NP_F A) (np _ a b c) ->
      e' = inject (subGF := sub_NP_F B) (np _ a' b' c') ->
      (forall (A' B' C' : Set) (f : A' -> C') (g : B' -> C')
        (a' a'' a''' : A') (b' b'' b''' : B'),
        f a' = g b' -> f a'' = g b'' -> f a''' = g b''' ->
        fmap f (np A' a' a'' a''') = fmap g (np B' b' b'' b''')) ->
      NP_Functor_eqv_S A B (mk_eqv_i _ _ gamma gamma' e e').

  Definition NP_Functor_eqv_P (A B : Set) (i : eqv_i A B) (x : NP_Functor_eqv_S A B i) : Type.
    destruct x.
    apply Empty_set.
    apply unit.
    apply (unit + unit)%type.
    apply (unit + unit + unit)%type.
  Defined.

  Definition NP_Functor_eqv_R (A B : Set) (i : eqv_i A B)
             (s : NP_Functor_eqv_S A B i)
             (p : NP_Functor_eqv_P A B i s) : eqv_i A B.
    destruct s; simpl in p.
    destruct p.
    apply (mk_eqv_i _ _ gamma gamma' a a').
    destruct p as [p|p].
    apply (mk_eqv_i _ _ gamma gamma' a a').
    apply (mk_eqv_i _ _ gamma gamma' b b').
    destruct p as [[p|p]|p].
    apply (mk_eqv_i _ _ gamma gamma' a a').
    apply (mk_eqv_i _ _ gamma gamma' b b').
    apply (mk_eqv_i _ _ gamma gamma' c c').
  Defined.

  Definition NP_Functor_eqv_to (A B : Set) (C : eqv_i A B -> Prop) (i : eqv_i A B) :
    IExt _ _ (NP_Functor_eqv_R A B) C i -> NP_Functor_eqv A B C i.
    refine(
    fun x => match x with
               | iext s pf =>
                 match s in NP_Functor_eqv_S _ _ i
                       return (forall p : NP_Functor_eqv_P A B i s,
                                 C (NP_Functor_eqv_R A B i s p)) ->
                              NP_Functor_eqv A B C i
                 with
                   | SNP_eqv_0 gamma gamma' e e' np np_all eq1 eq2 wf_np => fun pf' =>
                     NP_eqv_0 A B C gamma gamma' e e' np np_all eq1 eq2 wf_np
                   | SNP_eqv_1 gamma gamma' e e' np np_all a a' eq1 eq2 wf_np => fun pf' =>
                     NP_eqv_1 A B C gamma gamma' e e' np np_all a a' eq1 eq2 _ wf_np
                   | SNP_eqv_2 gamma gamma' e e' np np_all a a' b b' eq1 eq2 wf_np => fun pf' =>
                     NP_eqv_2 A B C gamma gamma' e e' np np_all a a' b b' eq1 eq2 _ _ wf_np
                   | SNP_eqv_3 gamma gamma' e e' np np_all a a' b b' c c' eq1 eq2 wf_np => fun pf' =>
                     NP_eqv_3 A B C gamma gamma' e e' np np_all a a' b b' c c' eq1 eq2 _ _ _ wf_np
                 end pf
             end); simpl in *.
    apply (pf' tt).
    apply (pf' (inl tt)).
    apply (pf' (inr tt)).
    apply (pf' (inl (inl tt))).
    apply (pf' (inl (inr tt))).
    apply (pf' (inr tt)).
  Defined.

  Definition NP_Functor_eqv_from (A B : Set) (C : eqv_i A B -> Prop) (i : eqv_i A B) :
    NP_Functor_eqv A B C i -> IExt _ _ (NP_Functor_eqv_R A B) C i.
    intro x.
    refine (match x in NP_Functor_eqv _ _ _ i return IExt _ _ (NP_Functor_eqv_R A B) C i
            with
              | NP_eqv_0 gamma gamma' e e' np np_all eq1 eq2 wf_np =>
                iext _ _ (SNP_eqv_0 _ _ gamma gamma' e e' np np_all eq1 eq2 wf_np) _
              | NP_eqv_1 gamma gamma' e e' np np_all a a' eq1 eq2 c1 wf_np =>
                iext _ _(SNP_eqv_1 _ _ gamma gamma' e e' np np_all a a' eq1 eq2 wf_np) _
              | NP_eqv_2 gamma gamma' e e' np np_all a a' b b' eq1 eq2 c1 c2 wf_np =>
                iext _ _(SNP_eqv_2 _ _ gamma gamma' e e' np np_all a a' b b' eq1 eq2 wf_np) _
              | NP_eqv_3 gamma gamma' e e' np np_all a a' b b' c c' eq1 eq2 c1 c2 c3 wf_np =>
                iext _ _(SNP_eqv_3 _ _ gamma gamma' e e' np np_all a a' b b' c c' eq1 eq2 wf_np) _
            end); simpl; intro p.
    destruct p.
    apply c1.
    destruct p as [p|p].
    apply c1.
    apply c2.
    destruct p as [[p|p]|p].
    apply c1.
    apply c2.
    apply c3.
  Defined.

  Global Instance NP_Functor_eqv_Container (A B : Set) : IContainer (NP_Functor_eqv A B) :=
    {| IS    := NP_Functor_eqv_S A B;
       IP    := NP_Functor_eqv_P A B;
       IR    := NP_Functor_eqv_R A B;
       ifrom := NP_Functor_eqv_from A B;
       ito   := NP_Functor_eqv_to A B
    |}.
  Proof.
    intros; destruct a; reflexivity.
    intros; destruct a; destruct s; simpl;
      apply f_equal; extensionality x; destruct x;
      try destruct s; try destruct u; reflexivity.
  Defined.


    Definition ind_alg_NP_Functor_eqv
      (A B : Set)
      (P : eqv_i A B -> Prop)
      (H : forall gamma gamma' e e' np np_all e_eq e'_eq wf_np,
        P (mk_eqv_i _ _ gamma gamma' e e'))
      (H0 : forall gamma gamma' e e' np np_all a a' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      (H1 : forall gamma gamma' e e' np np_all a a' b b' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _  gamma gamma' b b')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      (H2 : forall gamma gamma' e e' np np_all a a' b b' c c' e_eq e'_eq
        (IHa : P (mk_eqv_i _ _  gamma gamma' a a'))
        (IHb : P (mk_eqv_i _ _  gamma gamma' b b'))
        (IHc : P (mk_eqv_i _ _  gamma gamma' c c')) wf_np,
        P (mk_eqv_i _ _  gamma gamma' e e'))
      i (e : NP_Functor_eqv A B P i) : P i :=
      match e in NP_Functor_eqv _ _ _  i return P i with
        | NP_eqv_0 gamma gamma' e e' np np_all e_eq e'_eq wf_np =>
          H gamma gamma' e e' np np_all e_eq e'_eq wf_np
        | NP_eqv_1 gamma gamma' e e' np np_all a a' e_eq e'_eq a_eqv wf_np =>
          H0 gamma gamma' e e' np np_all a a' e_eq e'_eq a_eqv wf_np
        | NP_eqv_2 gamma gamma' e e' np np_all a a' b b' e_eq e'_eq a_eqv b_eqv wf_np =>
          H1 gamma gamma' e e' np np_all a a' b b' e_eq e'_eq a_eqv b_eqv wf_np
        | NP_eqv_3 gamma gamma' e e' np np_all a a' b b' c c' e_eq e'_eq a_eqv b_eqv c_eqv wf_np  =>
          H2 gamma gamma' e e' np np_all a a' b b' c c' e_eq e'_eq a_eqv b_eqv c_eqv wf_np
      end.

    (* Projection doesn't affect Equivalence Relation.*)

    Variable Sub_NP_Functor_eqv_EQV_E : forall A B,
      Sub_iFunctor (NP_Functor_eqv A B) (EQV_E A B).

   End eqv_Section.

   Variable EQV_E : forall A B, (@eqv_i A B -> Prop) -> eqv_i A B -> Prop.
   Context {ifun_EQV_E : forall A B, iFunctor (EQV_E A B)}.
   Context {ispf_EQV_E : forall A B, iSPF (EQV_E A B)}.
   Variable WFV : (WFValue_i D V -> Prop) -> WFValue_i D V -> Prop.
   Context `{spfWFV : iSPF _ WFV}.

   Definition WF_eqv_environment_P (env_A_B : Env (typeofR D) * Env nat) gamma'' :=
     (forall m b : nat,
       lookup (snd env_A_B) m = Some b ->
       exists T, lookup (fst env_A_B) b = Some T) /\
     Datatypes.length (fst env_A_B) = Datatypes.length (snd env_A_B) /\
     (forall m b : nat, lookup (snd env_A_B) m = Some b -> b = m) /\
     WF_Environment _ _ WFV gamma'' (fst env_A_B).

    Definition eqv_eval_alg_Soundness'_P
      (typeof_rec : Exp (E (typeofR D)) -> typeofR D)
      (eval_rec : Exp (E nat) -> evalR V)
      (typeof_F : Mixin (Exp (E (typeofR D))) (E (typeofR D)) (typeofR D))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalR V))
      (i : eqv_i (typeofR D) nat) :=
      E_eqv EQV_E _ _ i /\
      eval_alg_Soundness_P D V (E nat) WFV
      _ WF_eqv_environment_P
      (E (typeofR D)) (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec
      typeof_F eval_F
      (eqv_a _ _ i, eqv_b _ _ i).

    Lemma WF_eqv_environment_P_insert : forall gamma gamma' gamma'' v T,
      WF_eqv_environment_P (gamma, gamma') gamma'' ->
      WFValueC _ _ WFV v T ->
      WF_eqv_environment_P (insert _ (Some T) gamma, insert _ (Datatypes.length gamma') gamma')
      (insert _ v gamma'').
    Proof.
      intros; destruct H as [WF_gamma [WF_gamma2 [WF_gamma' WF_gamma'']]].
      unfold WF_eqv_environment_P; simpl in *|-*; repeat split.
      rewrite <- WF_gamma2.
      revert WF_gamma; clear; simpl; induction gamma';
        destruct m; simpl; intros; try discriminate.
      injection H; intros; subst.
      clear; induction gamma; simpl; eauto; eexists.
      injection H; intros; subst.
      generalize b (WF_gamma 0 _ (eq_refl _)); clear; induction gamma; simpl; intros b H;
        destruct H as [T' lookup_T']; try discriminate.
      destruct b; eauto.
      eapply IHgamma'.
      intros n0 b0 H0; eapply (WF_gamma (S n0) _ H0).
      eassumption.
      assert (exists m', Datatypes.length gamma' = m') as m'_eq
        by (eexists _; reflexivity); destruct m'_eq as [m' m'_eq].
      rewrite m'_eq; generalize m' gamma' WF_gamma2; clear; induction gamma;
        destruct gamma'; intros; simpl; try discriminate;
          try injection H7; intros; eauto.
      simpl in *|-*.
      intro; caseEq (beq_nat m (Datatypes.length gamma')).
      assert (exists m', m' = Datatypes.length gamma') as ex_m' by
        (eexists _; reflexivity); destruct ex_m' as [m' m'_eq];
          rewrite <- m'_eq in H at 1.
      rewrite <- WF_gamma2 in H1.
      rewrite (beq_nat_true _ _ H).
      rewrite (beq_nat_true _ _ H), m'_eq in H1.
      rewrite <- WF_gamma2 in m'_eq; rewrite m'_eq.
      generalize m' b H1; clear.
      induction gamma'; simpl; intros; try discriminate.
      injection H1; auto.
      eauto.
      eapply WF_gamma'.
      rewrite <- WF_gamma2 in H1.
      assert (exists m', m' = Datatypes.length gamma') as ex_m' by
      (eexists _; reflexivity); destruct ex_m' as [m' m'_eq].
      generalize m' m (beq_nat_false _ _ H) H1; clear;
        induction gamma'; simpl; destruct m; intros;
          try discriminate; eauto.
      elimtype False; eauto.
      eapply P2_Env_insert.
      eauto.
      apply H0.
    Qed.

    Section NP_beval_Soundness.

    Variable (NP : Set -> Set).
    Context `{PFun_NP : PFunctor NP}.
    Context {sub_NP_F : forall A, NP :<: E A}.
    Context {WF_sub_NP_F_V : forall A, WF_Functor _ _ (sub_NP_F A)}.

    Context {Sub_NP_Functor_eqv_EQV_E : forall A B,
      Sub_iFunctor (NP_Functor_eqv NP A B) (EQV_E A B)}.

    Context {eval_Soundness_alg_NP : forall pb typeof_rec eval_rec,
      FPAlgebra (eval_alg_Soundness_P D V (E nat) WFV _ WF_eqv_environment_P (E (typeofR D)) pb typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _)) (f_algebra (FAlgebra := beval_E))) (inject2 (F := NP))}.

    Variable WF_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot D V) WFV.

    Inductive eqv_eval_SoundnessName : Set := eqv_eval_soundnessname.

    Context {Typeof_NP : forall T, FAlgebra TypeofName T (typeofR D) NP}.
    Context {beval_NP : FAlgebra EvalName (Exp (E nat)) (evalR V) NP}.
    Context {WF_eval_F : @WF_FAlgebra EvalName _ _ NP (E _)
      (sub_NP_F _) beval_NP (eval_E _)}.
    Context {WF_typeof_F : @WF_FAlgebra TypeofName _ _ NP (E _)
      (sub_NP_F _) (Typeof_NP _) (Typeof_E (Fix' (E (typeofR D))))}.

    Global Instance eqv_eval_Soundness typeof_rec eval_rec :
      iPAlgebra eqv_eval_SoundnessName
      (eqv_eval_alg_Soundness'_P typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E))) (NP_Functor_eqv _ _ _).
    Proof.
      constructor; unfold iAlgebra; intros.
      apply (ind_alg_NP_Functor_eqv NP); try eassumption;
        unfold eqv_eval_alg_Soundness'_P; simpl; intros.
      (* NP_eqv_0 *)
      split.
      apply inject_i; econstructor; eauto.
      rewrite e_eq, e'_eq.
      generalize (p_algebra (FPAlgebra := eval_Soundness_alg_NP (gamma, gamma') typeof_rec eval_rec) (np _)).
      unfold inject2, Fix'.
      rewrite (wf_np _ _ _ (@fst (Fix' (E (typeofR D))) (Fix' (E nat))) id).
      rewrite (wf_np _ _ _ (@snd (Fix' (E (typeofR D))) (Fix' (E nat))) id).
      repeat rewrite fmap_id.
      intros H0; apply H0.
      apply np_all.
      (* NP_eqv_1 *)
      destruct IHa as [eqv_a IHa]; split; intros.
      apply inject_i; econstructor 2; eauto.
      rewrite e_eq, e'_eq.
      generalize (p_algebra (FPAlgebra := eval_Soundness_alg_NP (gamma, gamma') typeof_rec eval_rec) (np _ (a,a'))).
      unfold inject2, Fix'.
      rewrite (wf_np _ _ _ (@fst (Fix' (E (typeofR D))) (Fix' (E nat))) id _ a); auto.
      rewrite (wf_np _ _ _ (@snd (Fix' (E (typeofR D))) (Fix' (E nat))) id _ a'); auto.
      repeat rewrite fmap_id.
      intros H0; apply H0.
      apply np_all; auto.
      (* NP_eqv_2 *)
      destruct IHa as [a_eqv IHa]; destruct IHb as [b_eqv IHb].
      split; intros.
      apply inject_i; econstructor 3; eauto.
      rewrite e_eq, e'_eq.
      generalize (p_algebra (FPAlgebra := eval_Soundness_alg_NP (gamma, gamma') typeof_rec eval_rec) (np _ (a,a') (b,b'))).
      unfold inject2, Fix'.
      rewrite (wf_np _ _ _ (@fst (Fix' (E (typeofR D))) (Fix' (E nat))) id _ _ a b); auto.
      rewrite (wf_np _ _ _ (@snd (Fix' (E (typeofR D))) (Fix' (E nat))) id _ _ a' b'); auto.
      repeat rewrite fmap_id.
      intros H0; apply H0.
      apply np_all; auto.
      (* NP_eqv_3 *)
      destruct IHa as [a_eqv IHa]; destruct IHb as [b_eqv IHb]; destruct IHc as [c_eqv IHc].
      split; intros.
      apply inject_i; econstructor 4; eauto.
      rewrite e_eq, e'_eq.
      generalize (p_algebra (FPAlgebra := eval_Soundness_alg_NP (gamma, gamma') typeof_rec eval_rec) (np _ (a,a') (b,b') (c,c'))).
      unfold inject2, Fix'.
      rewrite (wf_np _ _ _ (@fst (Fix' (E (typeofR D))) (Fix' (E nat))) id _ _ _ a b c); auto.
      rewrite (wf_np _ _ _ (@snd (Fix' (E (typeofR D))) (Fix' (E nat))) id _ _ _ a' b' c'); auto.
      repeat rewrite fmap_id.
      intros H0; apply H0.
      apply np_all; auto.
    Qed.

    Context {eqv_eval_soundness_alg : forall typeof_rec eval_rec,
      iPAlgebra eqv_eval_SoundnessName
      (eqv_eval_alg_Soundness'_P
        typeof_rec eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := eval_E _))) (EQV_E _ _)}.

    Definition eqv_eval_soundness_P (i : eqv_i (typeofR D) nat) :=
      forall (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (env_B _ _ i) n = Some b ->
          exists T, lookup (env_A _ _ i) b = Some T)
        (WF_gamma2 : List.length (env_A _ _ i) = List.length (env_B _ _ i))
        (WF_gamma' : forall n b, lookup (env_B _ _ i) n = Some b -> b = n)
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (env_A _ _ i)) T,
        typeof _ _ (eqv_a _ _ i) = Some T ->
        WFValueC _ _ WFV (eval (eval_E := eval_E)
          V _ (eqv_b _ _ i) gamma'') T.

    Variable (WF_MAlg_typeof : WF_MAlgebra Typeof_E).
    Variable (WF_MAlg_eval : WF_MAlgebra eval_E).

    Lemma eqv_eval_soundness' : forall gamma gamma' e' e'',
      E_eqvC EQV_E gamma gamma' e' e'' ->
      eqv_eval_soundness_P (mk_eqv_i _ _ gamma gamma' e' e'').
    Proof.
      intros; generalize (ifold_
        (if_algebra (iPAlgebra := eqv_eval_soundness_alg
          (fun e => typeof D (E (typeofR D)) e)
          (fun e => eval V (E nat) e))) (mk_eqv_i _ _ gamma gamma' e' e'') H).
      unfold eqv_eval_alg_Soundness'_P, eqv_eval_soundness_P; simpl;
        intros.
      revert H1.
      rewrite <- (in_out_inverse e'').
      unfold eval.
      rewrite fold_computation.
      rewrite wf_malgebra.
      unfold id at 1; simpl.
      unfold eval_alg_Soundness_P in H0.
      intros; eapply H0; unfold WF_eqv_environment_P.
      split; eauto.
      intros.
      unfold eval.
      revert H3.
      rewrite <- (in_out_inverse (fst a)).
      unfold typeof.
      rewrite fold_computation, wf_malgebra.
      unfold id at 1; simpl.
      intros.
      destruct a; simpl.
      rewrite <- (in_out_inverse e).
      rewrite fold_computation, wf_malgebra.
      unfold id at 1; simpl.
      apply H2.
      apply H3.
      unfold typeof in H1.
      rewrite <- (in_out_inverse e'), fold_computation, wf_malgebra in H1.
      apply H1.
    Qed.

    Lemma eqv_eval_soundness : forall gamma gamma' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' ->
      forall (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (gamma') n = Some b ->
          exists T, lookup (gamma) b = Some T)
        (WF_gamma2 : List.length (gamma) = List.length (gamma'))
        (WF_gamma' : forall n b, lookup (gamma') n = Some b -> b = n)
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (gamma)) T,
        typeof _ _ e' = Some T ->
        WFValueC _ _ WFV (eval (eval_E := eval_E)
          V _ e'' gamma'') T.
    Proof.
      intros; eapply eqv_eval_soundness'; eauto.
    Qed.

    Definition soundness_X'_P
      (typeof_rec : Exp (E (typeofR D)) -> typeofR D)
      (eval_rec : Exp (E nat) -> evalR V)
      (typeof_F : Mixin (Exp (E (typeofR D))) (E (typeofR D)) (typeofR D))
      (eval_F : Mixin (Exp (E nat)) (E nat) (evalR V))
      i :=
      forall (IH : forall (e : Exp _) (e' : Exp _)
        pb gamma'' (WF_gamma'' : WF_eqv_environment_P pb gamma'')
        T,
        E_eqvC EQV_E (fst pb) (snd pb) e e' ->
        typeof_rec e = Some T ->
        WFValueC _ _ WFV (eval_rec e' gamma'') T),
      E_eqv EQV_E _ _ i /\
      eval_alg_Soundness_P D V (E nat) WFV
      _ WF_eqv_environment_P
      (E (typeofR D)) (env_A _ _ i, env_B _ _ i) typeof_rec eval_rec
      typeof_F eval_F
      (eqv_a _ _ i, eqv_b _ _ i).

    Inductive soundness_XName : Set := soundness_Xname.

    Global Instance Lift_soundness_X_alg
      typeof_rec eval_rec typeof_alg eval_alg
      EQV_G {fun_EQV_G : iFunctor EQV_G}
      {EQV_G_EQV_Alg : iPAlgebra eqv_eval_SoundnessName
        (eqv_eval_alg_Soundness'_P typeof_rec eval_rec typeof_alg eval_alg) EQV_G} :
        iPAlgebra soundness_XName
        (soundness_X'_P
          typeof_rec eval_rec typeof_alg eval_alg) EQV_G.
      intros; econstructor; generalize (if_algebra); unfold iAlgebra; intros.
      unfold soundness_X'_P; intros.
      assert (EQV_G (eqv_eval_alg_Soundness'_P typeof_rec eval_rec typeof_alg eval_alg) i).
      eapply ifmap; try eapply H0.
      intros; apply H1; apply IH.
      apply (H _ H1).
    Defined.

    Context {soundness_X_alg : forall eval_rec,
      iPAlgebra soundness_XName
      (soundness_X'_P
        (typeof _ _) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E))) (EQV_E _ _)}.
    Variable Sub_WFV_Bot_WFV : Sub_iFunctor (WFValue_Bot _ _) WFV.

    Definition soundness_X_P (i : eqv_i (typeofR D) nat) :=
      forall n (gamma'' : Env _)
        (WF_gamma : forall n b, lookup (env_B _ _ i) n = Some b ->
          exists T, lookup (env_A _ _ i) b = Some T)
        (WF_gamma2 : List.length (env_A _ _ i) = List.length (env_B _ _ i))
        (WF_gamma' : forall n b, lookup (env_B _ _ i) n = Some b -> b = n)
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' (env_A _ _ i)) T,
        typeof _ _ (eqv_a _ _ i) = Some T ->
        WFValueC _ _ WFV (beval V (E _) n (beval_E := beval_E)
          (eqv_b _ _ i) gamma'') T.

    Lemma soundness_X' :
      forall eval_rec gamma gamma' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' ->
        soundness_X'_P (typeof _ _) eval_rec
        (f_algebra (FAlgebra := Typeof_E _))
        (f_algebra (FAlgebra := beval_E)) (mk_eqv_i _ _ gamma gamma' e' e'').
    Proof.
      intros; apply (ifold_); try assumption.
      apply if_algebra.
    Qed.

    Variable SV : (SubValue_i V -> Prop) -> SubValue_i V -> Prop.
    Context `{ispf_SV : iSPF _ SV}.
    Context {Sub_SV_Bot_SV : Sub_iFunctor (SubValue_Bot V) SV}.
    Context {Sub_SV_refl_SV : Sub_iFunctor (SubValue_refl V) SV}.

    Context {WF_Value_continous_alg :
      iPAlgebra WFV_ContinuousName (WF_Value_continuous_P D V WFV) SV}.
    Context {eval_continuous_Exp_E : FPAlgebra
       (eval_continuous_Exp_P V (E nat) SV) (inject' (E nat))}.

    Lemma soundness_X :
      forall n gamma gamma' gamma'' e' e'',
        E_eqvC EQV_E gamma gamma' e' e'' ->
        forall (WF_gamma : forall n b, lookup gamma' n = Some b ->
          exists T, lookup gamma b = Some T)
        (WF_gamma2 : List.length gamma = List.length gamma')
        (WF_gamma' : forall n b, lookup gamma' n = Some b -> b = n)
        (WF_gamma'' : WF_Environment _ _ WFV gamma'' gamma) T,
        typeof _ _ e' = Some T ->
        WFValueC _ _ WFV (beval V (E _) n (beval_E := beval_E)
          e'' gamma'') T.
    Proof.
      induction n; simpl;
          intros; unfold beval; simpl in *|-*.
      apply (inject_i (subGF := Sub_WFV_Bot_WFV)); econstructor; eauto.
      generalize (soundness_X' (beval V (E _) n) _ _ _ _ H).
      unfold soundness_X'_P;
        unfold eval_alg_Soundness_P; simpl; intros.
      apply H1; auto.
      unfold beval; intros;
      destruct WF_gamma''0 as [WF_pb [WF_pb2 [WF_pb' WF_gamma''0]]].
      eapply IHn; eauto.
      repeat split; auto.
      intros.
      destruct a as [a a'].
      simpl in *|-*.
      apply (WF_Value_beval D V (E _) SV _ WFV n (S n) _ gamma''0); auto.
      apply Sub_Environment_refl; auto.
      apply H2.
      unfold typeof in H3.
      rewrite <- (in_out_inverse a) in H3.
      rewrite fold_computation, wf_malgebra in H3.
      unfold id at 1 in H3; simpl in H3; try rewrite <- eta_expansion in H3.
      unfold typeof.
      apply H3.
      unfold typeof in H0.
      rewrite <- (in_out_inverse e') in H0.
      rewrite fold_computation, wf_malgebra in H0.
      unfold id at 1 in H0; simpl in H0; try rewrite <- eta_expansion in H0.
      apply H0.
    Qed.

  End NP_beval_Soundness.

End PNames.
