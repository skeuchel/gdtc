Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FJ_tactics.

Section Sums.

  Definition fold_sum {A B : Type} {C : sum A B -> Type}
             (f : forall (a : A), C (inl _ a))
             (g : forall (b : B), C (inr _ b))
             (x : A + B) : C x :=
    match x with
    | inl y => f y
    | inr y => g y
    end.

  Definition fold_sum' {A B : Type} {C : Type}
    (f : A -> C) (g : B -> C) (x : A + B) : C :=
    @fold_sum A B (fun _ => C) f g x.

  Definition map_sum {A B C D : Type} (f : A -> C) (g : B -> D)
    (x : A + B) : C + D :=
    fold_sum (fun x => inl _ (f x)) (fun x => inr _ (g x)) x.

End Sums.

Section Functors.
  Class Functor (F : Set -> Set) :=
    { fmap :
        forall {A B : Set} (f : A -> B), F A -> F B;
      fmap_fusion :
        forall (A B C: Set) (f : A -> B) (g : B -> C) (a : F A),
          fmap g (fmap f a) = fmap (fun e => g (f e)) a;
      fmap_id :
        forall (A : Set) (a : F A),
          fmap (@id A) a = a
    }.

  Lemma fmap_id' (F : Set -> Set) {Fun_F : Functor F} (A : Set) (f : A -> A) :
    (forall a, f a = a) -> (forall a, fmap f a = a).
  Proof.
    destruct Fun_F.
    intros H fa.
    cut (f = id); intros; subst.
    apply fmap_id.
    apply functional_extensionality.
    assumption.
  Qed.

  Class iFunctor {I : Set} (F : (I -> Prop) -> I -> Prop) :=
    { ifmap :
        forall {A B : I -> Prop} i (f : forall i, A i -> B i), F A i -> F B i;
      ifmap_fusion :
        forall (A B C: I -> Prop) i (f : forall i, A i -> B i) (g : forall i, B i -> C i) (a : F A i),
          ifmap i g (ifmap i f a) = ifmap i (fun i e => g _ (f i e)) a;
      ifmap_id :
        forall (A : I -> Prop) i (a : F A i),
          ifmap i (fun _ => id) a = a
    }.

  (* ============================================== *)
  (* FUNCTOR COMPOSITION                            *)
  (* ============================================== *)

  Definition inj_Functor (F G : Set -> Set) (A : Set) : Set := sum (F A) (G A).
  Definition prod_Functor (F G : Set -> Set) (A : Set) : Set := prod (F A) (G A).

  Notation "A :+: B" := (inj_Functor A B) (at level 80, right associativity).
  Notation "A :*: B" := (prod_Functor A B) (at level 70, right associativity).

  Class Sub_Functor (F G : Set -> Set) : Type :=
    { inj : forall {A : Set}, F A -> G A;
      prj : forall {A : Set}, G A -> option (F A);
      inj_prj : forall {A : Set} (ga : G A) (fa : F A),
        prj ga = Some fa -> ga = inj fa;
      prj_inj : forall {A : Set} (fa : F A),
        prj (inj fa) = Some fa
    }.

  Notation "A :<: B"  := (Sub_Functor A B) (at level 80, right associativity).

  (* Need the 'Global' modifier so that the instance survives the Section.*)
  Global Instance Sub_Functor_inl (F G H : Set -> Set) (sub_F_G : F :<: G) :
    F :<: (G :+: H) :=
    {| inj := fun (A : Set) (e : F A) => inl _ (inj (Sub_Functor := sub_F_G) e);
       prj := fun (A: Set) (e : (G :+: H) A) =>
                match e with
                  | inl e' => prj e'
                  | inr _  => None
                end
    |}.
  Proof.
    intros; destruct ga; [rewrite (inj_prj _ _ H0); reflexivity | discriminate].
    intros; simpl; rewrite prj_inj; reflexivity.
  Defined.

  Global Instance Sub_Functor_inr (F G H : Set -> Set) (sub_F_H : F :<: H) :
    F :<: (G :+: H) :=
    {| inj := fun (A : Set) (e : F A) => inr _ (inj (Sub_Functor := sub_F_H) e);
       prj := fun (A : Set) (e : (G :+: H) A) =>
                match e with
                  | inl _  => None
                  | inr e' => prj e'
                end
    |}.
  Proof.
    intros; destruct ga; [discriminate | rewrite (inj_prj _ _ H0); reflexivity ].
    intros; simpl; rewrite prj_inj; reflexivity.
  Defined.

  Global Instance Sub_Functor_id {F : Set -> Set} : F :<: F :=
    {| inj := fun A => @id (F A);
       prj := fun A => @Some (F A)
    |}.
  Proof.
    unfold id; congruence.
    reflexivity.
  Defined.

  (* ============================================== *)
  (* WELL-FORMEDNESS OF FUNCTORS                    *)
  (* ============================================== *)

  Class WF_Functor (F G: Set -> Set)
    (subfg: F :<: G)
    {Fun_F: Functor F}
    {Fun_G: Functor G} : Prop :=
    { wf_functor :
        forall (A B : Set) (f : A -> B) (fa: F A) ,
          fmap f (inj fa) (F := G) = inj (fmap f fa)
    }.

  Global Instance WF_Functor_id {F : Set -> Set} {Fun_F : Functor F} :
    WF_Functor F F Sub_Functor_id.
  Proof.
    econstructor; intros; reflexivity.
  Defined.

  (*
  Global Instance WF_Functor_plus_inl {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {subfg : F :<: G}
    {WF_Fun_F : WF_Functor F _ subfg}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inl F G H _).
  Proof.
    econstructor; intros.
    simpl; rewrite wf_functor; reflexivity.
  Defined.

  Global Instance WF_Functor_plus_inr {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {subfh : F :<: H}
    {WF_Fun_F : WF_Functor F _ subfh}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inr F G H _ ).
  Proof.
    econstructor; intros.
    simpl; rewrite wf_functor; reflexivity.
  Defined.
  *)

  Class Distinct_Sub_Functor (F G H : Set -> Set)
    {sub_F_H : F :<: H}
    {sub_G_H : G :<: H}
    : Prop :=
    { inj_discriminate :
        forall {A : Set} (f : F A) (g : G A),
             inj (Sub_Functor := sub_F_H) f
          <> inj (Sub_Functor := sub_G_H) g
    }.

  Global Instance Distinct_Sub_Functor_plus
    (F G H I : Set -> Set)
    (sub_F_G : F :<: G)
    (sub_H_I : H :<: I)
    :
    Distinct_Sub_Functor F H (G :+: I).
  Proof.
    constructor; discriminate.
  Defined.

  Global Instance Distinct_Sub_Functor_plus'
    (F G H I : Set -> Set)
    (sub_F_G : F :<: G)
    (sub_H_I : H :<: I)
    :
    Distinct_Sub_Functor F H (I :+: G).
  Proof.
    constructor; discriminate.
  Defined.

  Global Instance Distinct_Sub_Functor_inl
    (F G H I : Set -> Set)
    (sub_F_G : F :<: G)
    (sub_H_G : H :<: G)
    (Dist_inl : Distinct_Sub_Functor F H G)
    :
    Distinct_Sub_Functor F H (G :+: I).
  Proof.
    constructor; unfold not; simpl; intros.
    injection H0; intros.
    apply (inj_discriminate _ _ H1).
  Defined.

  Global Instance Distinct_Sub_Functor_inr
    (F G H I : Set -> Set)
    (sub_F_G : F :<: G)
    (sub_H_G : H :<: G)
    (Dist_inl : Distinct_Sub_Functor F H G)
    :
    Distinct_Sub_Functor F H (I :+: G).
  Proof.
    constructor; unfold not; simpl; intros.
    injection H0; intros.
    apply (inj_discriminate _ _ H1).
  Defined.

  (* ============================================== *)
  (* INDEXED FUNCTOR COMPOSITION                    *)
  (* ============================================== *)

  Definition inj_iFunctor {I : Set} (F G : (I -> Prop) -> I -> Prop) :
    (I -> Prop) -> (I -> Prop) :=
    fun A i => or (F A i) (G A i).

  Notation "A ::+:: B" := (inj_iFunctor A B) (at level 80, right associativity).

  Global Instance iFunctor_Plus
    {I : Set} (G H : (I -> Prop) -> I -> Prop)
    {Fun_G : iFunctor G} {Fun_H : iFunctor H}
  : iFunctor (G ::+:: H) :=
    {| ifmap :=
         fun (A B : I -> Prop) (i : I)
             (f : forall i, A i -> B i)
             (a : (G ::+:: H) A i) =>
           match a with
             | or_introl G' => or_introl _ (ifmap i f G')
             | or_intror H' => or_intror _ (ifmap i f H')
           end
    |}.
  Proof.
    (* ifmap_fusion *)
    intros; destruct a;
    rewrite ifmap_fusion; reflexivity.
    (* ifmap_id *)
    intros; destruct a;
    rewrite ifmap_id; reflexivity.
  Defined.

  Class Sub_iFunctor {I : Type} (F G : (I -> Prop) -> I -> Prop) : Prop :=
    { inj_i : forall {A : I -> Prop} i, F A i -> G A i;
      prj_i : forall {A : I -> Prop} i, G A i -> (F A i) \/ True
    }.

  Notation "A ::<:: B" := (Sub_iFunctor A B) (at level 80, right associativity).

  (* Need the 'Global' modifier so that the instance survives the Section.*)

  Global Instance Sub_iFunctor_inl {I' : Set}
    (F G H : (I' -> Prop) -> I' -> Prop) (subFG : F ::<:: G)
  : F ::<:: (G ::+:: H) :=
    {| inj_i := fun (A: I' -> Prop) i (e : F A i) =>
                  or_introl _ (inj_i _ e);
       prj_i := fun (A: I' -> Prop) i (e : (G ::+:: H) A i) =>
                  match e with
                    | or_introl e' => prj_i _ e'
                    | or_intror _  => or_intror _ I
                  end
    |}.

  Global Instance Sub_iFunctor_inr {I' : Set}
    (F G H : (I' -> Prop) -> I' -> Prop) (sub_F_H : F ::<:: H)
  : F ::<:: (G ::+:: H) :=
    {| inj_i := fun (A: I' -> Prop) i (e : F A i) =>
                  or_intror _ (inj_i _ e);
       prj_i := fun (A: I' -> Prop) i (e : (G ::+:: H) A i) =>
                  match e with
                    | or_intror e' => prj_i _ e'
                    | or_introl _  => or_intror _ I
                  end
    |}.

  Global Instance Sub_iFunctor_id {I : Set}
    (F : (I -> Prop) -> I -> Prop) : F ::<:: F :=
    {| inj_i := fun A i e => e;
       prj_i := fun A i e => or_introl _ e
    |}.

End Functors.

Notation "A :+: B" := (inj_Functor A B) (at level 80, right associativity).
Notation "A :*: B" := (prod_Functor A B) (at level 70, right associativity).
Notation "A :<: B" := (Sub_Functor A B) (at level 80, right associativity).
Notation "A ::+:: B" := (inj_iFunctor A B) (at level 80, right associativity).
Notation "A ::<:: B" := (Sub_iFunctor A B) (at level 80, right associativity).

Section Folds.

  Class PFunctor (F : Set -> Set) {Fun_F : Functor F} :=
  { All : forall {A : Set} (Q : A -> Prop) , F A -> Prop;
    All_fmap {A B : Set} (f : A -> B) (Q : B -> Prop) (xs : F A) :
      All (fun x => Q (f x)) xs <-> All Q (fmap f xs)
  }.

  (*
  Class iPFunctor {I : Type} (F : (I -> Prop) -> I -> Prop) :=
  { iAll : forall {A : I -> Prop} (Q : forall i, A i -> Prop) i, F A i -> Prop
  }.
  *)

  (* ============================================== *)
  (* ALGEBRAS                                       *)
  (* ============================================== *)

  (* Ordinary Algebra *)
  Definition Algebra (F: Set -> Set) (A : Set) :=
    F A -> A.

  (* Proof Algebra *)
  Definition PAlgebra
             {F : Set -> Set} `{PFunctor F}
             {A : Set} (f : Algebra F A) (Q : A -> Prop) : Set :=
    forall xs : F A, All Q xs -> Q (f xs).

  (* Mixin Algebra *)
  Definition Mixin (T: Set) (F: Set -> Set) (A : Set) :=
    (T -> A) -> F T -> A.

  (* Mixin Proof Algebra *)
  Definition PMixin (T : Set)
    (F : Set -> Set) {Fun_F : Functor F} {PFun_F : PFunctor F} {T A : Set}
    (f : Mixin T F A) (P : T -> Prop) (Q : A -> Prop) : Set :=
    forall (rec : T -> A) (xs : F T),
      (forall t, P t -> Q (rec t)) -> All P xs -> Q (f rec xs).

  (* Mendler Algebra *)
  Definition MAlgebra (F: Set -> Set) (A : Set) :=
    forall (R : Set), Mixin R F A.

  Definition MAlg_to_Alg {F : Set -> Set} {A : Set} :
    MAlgebra F A -> Algebra F A := fun MAlg => MAlg A id.

  (* Indexed Algebra *)
  Definition iAlgebra {I: Type} (F: (I -> Prop) -> I -> Prop) (A: I -> Prop) :=
    forall i, F A i -> A i.

  (* Indexed Mendler Algebra *)
  Definition iMAlgebra {I : Type} (F: (I -> Prop) -> I -> Prop) (A: I -> Prop) :=
    forall i (R : I -> Prop),
      (forall i, R i -> A i) -> F R i -> A i.

  Definition Algebra_Plus {F G : Set -> Set} {A : Set}
    (falg : Algebra F A) (galg : Algebra G A) : Algebra (F :+: G) A :=
    fun x => match x with
             | inl f => falg f
             | inr g => galg g
             end.
  Notation "f >+< g" := (Algebra_Plus f g) (at level 80, right associativity).

  Definition Mixin_Plus {F G : Set -> Set} {T A : Set}
    (falg : Mixin T F A) (galg : Mixin T G A) : Mixin T (F :+: G) A :=
    fun rec x => match x with
                 | inl f => falg rec f
                 | inr g => galg rec g
                 end.
  Notation "f >++< g" := (Mixin_Plus f g) (at level 80, right associativity).

  Class WF_Algebra {A: Set} (F G: Set -> Set)
    (subfg: F :<: G) (falg: Algebra F A) (galg: Algebra G A) : Prop :=
    { wf_algebra :
        forall (fa: F A), galg (inj fa) = falg fa
    }.

  Global Instance WF_Algebra_id {A : Set} {F} {falg: Algebra F A}:
    WF_Algebra F F Sub_Functor_id falg falg.
  Proof.
    constructor; auto.
  Defined.

  Global Instance WF_Algebra_inl
    {A : Set}
    {F G H}
    {falg: Algebra F A}
    {galg: Algebra G A}
    {halg: Algebra H A}
    {subFG: F :<: G}
    {wf_FG: WF_Algebra F G subFG falg galg}
    :
    WF_Algebra F (G :+: H) (Sub_Functor_inl F G H subFG) falg (galg >+< halg).
  Proof.
    constructor; unfold inj; simpl; intros.
    apply (wf_algebra fa).
  Defined.

  Global Instance WF_Algebra_inr
    {A : Set}
    {F G H}
    {falg: Algebra F A}
    {galg: Algebra G A}
    {halg: Algebra H A}
    {sub_F_H: F :<: H}
    {wf_G_H: WF_Algebra F H sub_F_H falg halg}
    :
    WF_Algebra F (G :+: H) (Sub_Functor_inr F G H sub_F_H) falg (galg >+< halg).
  Proof.
    constructor; unfold inj; simpl; intros.
    apply (wf_algebra fa).
  Defined.

  Class WF_Mixin (T A: Set) (F G: Set -> Set)
    (subfg: F :<: G)
    (falg: Mixin T F A)
    (galg: Mixin T G A): Set :=
    { wf_mixin :
      forall rec (fa: F T),
        galg rec (inj fa) = falg rec fa
    }.

  Global Instance WF_Mixin_id {T A : Set} {F} {falg: Mixin T F A}:
    WF_Mixin T A F F Sub_Functor_id falg falg.
  Proof.
    constructor; auto.
  Defined.

  Global Instance WF_Mixin_inl
    {T A : Set}
    {F G H}
    {falg: Mixin T F A}
    {galg: Mixin T G A}
    {halg: Mixin T H A}
    {sub_FG: F :<: G}
    {wf_FG: WF_Mixin T A F G sub_FG falg galg}
    :
    WF_Mixin T A F (G :+: H) (Sub_Functor_inl F G H sub_FG) falg (galg >++< halg).
  Proof.
    constructor; unfold inj; simpl; intros.
    apply (wf_mixin rec fa).
  Defined.

  Global Instance WF_Mixin_inr
    {T A : Set}
    {F G H}
    {falg: Mixin T F A}
    {galg: Mixin T G A}
    {halg: Mixin T H A}
    {sub_FH: F :<: H}
    {wf_GH: WF_Mixin T A F H sub_FH falg halg}
    :
    WF_Mixin T A F (G :+: H) (Sub_Functor_inr F G H sub_FH) falg (galg >++< halg).
  Proof.
    constructor; unfold inj; simpl; intros.
    apply (wf_mixin rec fa).
  Defined.

  (* ============================================== *)
  (* FOLDS                                          *)
  (* ============================================== *)

  Class SPF (F : Set -> Set) {Fun_F : Functor F} {PFun_F : PFunctor F} :=
  { Fix              : Set;
    in_t             : F Fix -> Fix;
    out_t            : Fix -> F Fix;

    fold_            : forall {A : Set}, Algebra F A -> Fix -> A;
    foldp            : forall {A : Set} {f : Algebra F A} {Q : A -> Prop},
                         PAlgebra f Q -> forall x, Q (fold_ f x);

    in_out_inverse   : forall (e : Fix), in_t (out_t e) = e;
    out_in_inverse   : forall (e : F (Fix)), out_t (in_t e) = e;

    fold_uniqueness  : forall {A : Set} (f : Algebra F A) (h : Fix -> A),
                         (forall e : F (Fix), h (in_t e) = f (fmap h e)) ->
                         forall (x : Fix), h x = fold_ f x;
    fold_computation : forall {A : Set} (f : Algebra F A) (a : F (Fix)),
                         fold_ f (in_t a) = f (fmap (fold_ f) a)
  }.

  Global Arguments Fix F {_ _ _}.

  Class iSPF {I : Set} (F : (I -> Prop) -> I -> Prop) `{ifunctor : iFunctor _ F} :=
  { iFix             : I -> Prop;
    in_ti            : forall i, F iFix i -> iFix i;
    out_ti           : forall i, iFix i -> F iFix i;

    ifold_           : forall {A : I -> Prop}, iAlgebra F A -> forall i, iFix i -> A i;

    in_out_inversei  : forall (i : I) (e : iFix i), in_ti i (out_ti i e) = e;
    out_in_inversei  : forall (i : I) (e : F iFix i), @out_ti i (in_ti i e) = e

(*
    ifoldp           : forall {A : Set} {f : Algebra F A} {Q : A -> Prop},
                         PAlgebra f Q -> forall x, Q (fold_ f x);


    fold_uniqueness  : forall {A : Set} (f : Algebra F A) (h : Fix -> A),
                         (forall e : F (Fix), h (in_t e) = f (fmap h e)) ->
                         forall (x : Fix), h x = fold_ f x;
    fold_computation : forall {A : Set} (f : Algebra F A) (a : F (Fix)),
                         fold_ f (in_t a) = f (fmap (fold_ f) a) *)
  }.

  Global Arguments iFix {I} F {_ _} i.

  Fixpoint boundedFix {A: Set} {F: Set -> Set} `{spf_F: SPF F}
    (n : nat) (fM: Mixin (Fix F) F A) (default: A) (e: Fix F): A :=
    match n with
      | 0   => default
      | S n => fM (boundedFix n fM default) (out_t e)
    end.

  Definition inject F G `{spf_G : SPF G} {subFG: F :<: G} :
    F (Fix G) -> Fix G := fun exp => in_t (inj exp).

  Definition project F G `{spf_G : SPF G} {subFG: F :<: G} :
    Fix G -> option (F (Fix G)) := fun exp => prj (out_t exp).

  Lemma inject_in_t F `{spf_F : SPF F} :
    inject F F = in_t.
  Proof.
    now extensionality x.
  Qed.

  Lemma inject_project
        (G H : Set -> Set) `{spf_H : SPF H}
        {sub_G_H : G :<: H} :
    forall (h : Fix H) (g : G (Fix H)),
      project _ _ h = Some g -> h = inject _ _ g.
  Proof.
    unfold inject, project; simpl; intros ? ? Heq.
    apply inj_prj in Heq.
    now rewrite <- Heq, in_out_inverse.
  Qed.

  Lemma project_inject (F G  : Set -> Set)
    `(spf_F : SPF F) (sub_G_F : G :<: F) :
    forall (g : G (Fix F)),
      project _ _ (inject _ _ g) = Some g.
  Proof.
    unfold project, inject; simpl; intros.
    now rewrite out_in_inverse, prj_inj.
  Qed.

  Lemma inject_inject (G H : Set -> Set)
    `{spf_H : SPF H} {sub_G_H : G :<: H} :
    forall (g1 g2 : G (Fix H)),
      inject _ _ g1 = inject _ _ g2 -> g1 = g2.
  Proof.
    intros ? ? Heq.
    apply (f_equal (project _ _)) in Heq.
    repeat rewrite project_inject in Heq.
    congruence.
  Qed.

  Definition inject_i {I F G} `{spf_F : iSPF I F} {subGF: Sub_iFunctor G F } :
    forall i, G (iFix F) i -> iFix F i := fun i gexp => in_ti i (inj_i i gexp).

  Definition project_i {I F G} `{spf_F : iSPF I F} {subGF: Sub_iFunctor G F } :
    forall i, iFix F i -> (G (iFix F) i) \/ True :=
      fun i fexp => prj_i i (out_ti i fexp).

  Section DerivedLaws.

    Variable F : Set -> Set.
    Context `{SPF_F : SPF F}.

    Lemma fold_reflection (e : Fix F) :
      fold_ in_t e = e.
    Proof.
      apply sym_eq.
      rewrite <- (in_out_inverse e).
      apply (fold_uniqueness in_t (fun x => x)).
      intros e0.
      rewrite fmap_id.
      reflexivity.
    Qed.

    Lemma fold_fusion (e : Fix F) :
      forall (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B),
        (forall a, h (f a) = g (fmap h a)) ->
        (fun e' => h (fold_ f e')) e = fold_ g e.
    Proof.
      intros.
      apply fold_uniqueness.
      intros.
      now rewrite fold_computation, H, fmap_fusion.
    Qed.

    Lemma Universal_Property_fold (B : Set)
      (f : Algebra F B) : forall (h : Fix F -> B), h = fold_ f ->
        forall e, h (in_t e) = f (fmap h e).
    Proof.
      intros ? Heq; rewrite Heq.
      now apply fold_computation.
    Qed.

    Lemma Universal_Property'_fold (e : Fix F) :
      forall (B : Set) (f : Algebra F B) (h : Fix F -> B),
        (forall e, h (in_t e) = f (fmap h e)) ->
        h e = fold_ f e.
    Proof.
      intros.
      now apply fold_uniqueness.
    Qed.

    Lemma in_t_inject {e e' : F (Fix F)} :
      in_t e = in_t e' -> e = e'.
    Proof.
      intros; apply (f_equal out_t) in H;
        repeat rewrite out_in_inverse in H; auto.
    Qed.

    Lemma out_fold_fmap_in :
      out_t = fold_ (fmap in_t).
    Proof.
      extensionality x.
      apply fold_uniqueness.
      intros.
      rewrite out_in_inverse.
      rewrite fmap_fusion.
      rewrite fmap_id'; auto.
      apply in_out_inverse.
    Qed.

    Lemma ind {Q : Fix F -> Prop} (step : PAlgebra in_t Q) (x : Fix F) : Q x.
    Proof.
      rewrite <- fold_reflection.
      apply (foldp step).
    Qed.

  End DerivedLaws.

  (*
  Global Instance PFunctor_Plus G H `{pfun_G : PFunctor G} `{pfun_H : PFunctor H} :
    PFunctor (G :+: H) := {| All := fun A Q x =>
                                      match x with
                                        | inl f => All Q f
                                        | inr g => All Q g
                                      end |}.
  *)

  (*
  Lemma PAlgebra_Plus {F G : Set -> Set} `{PFunctor F} `{PFunctor G}
        {A : Set} {falg : Algebra F A} {galg : Algebra G A}
        (Q : A -> Prop) (fpalg : PAlgebra falg Q) (gpalg : PAlgebra galg Q) :
    PAlgebra (Algebra_Plus falg galg) Q.
  Proof.
    intros xs; destruct xs; simpl; auto.
  Defined.
  *)

  Definition iAlgebra_Plus {I : Set} {F G : (I -> Prop) -> I -> Prop} {A : I -> Prop}
             (falg : iAlgebra F A) (galg : iAlgebra G A) : iAlgebra (F ::+:: G) A :=
    fun i x =>
      match x with
        | or_introl f => falg _ f
        | or_intror g => galg _ g
      end.

  Lemma inject_discriminate
    {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    `{SPF_H : SPF H}
    {sub_FH : F :<: H}
    {sub_GH : G :<: H}
    {WF_F : WF_Functor F H _}
    {WF_G : WF_Functor G H _}
    (Dist_FGH : Distinct_Sub_Functor F G H)
  : forall f g,
      inject _ _ (subFG := sub_FH) f
      <> inject _ _ (subFG := sub_GH) g.
  Proof.
    unfold inject; intros; intro eq.
    apply (inj_discriminate f g).
    apply (in_t_inject _ eq).
  Qed.

End Folds.

Section FAlgebra.

  (* ============================================== *)
  (* OPERATIONS INFRASTRUCTURE                      *)
  (* ============================================== *)

  Class FAlgebra (Name : Set) (T: Set) (A: Set) (F: Set -> Set) : Set :=
    { f_algebra : Mixin T F A }.

  Global Instance FAlgebra_Plus (Name: Set) (T: Set) (A : Set) (F G : Set -> Set)
    {falg: FAlgebra Name T A F} {galg: FAlgebra Name T A G} :
    FAlgebra Name T A (F :+: G) | 6 :=
    {| f_algebra := Mixin_Plus f_algebra f_algebra |}.

  (* The | 6 gives the generated Hint a priority of 6. If this is
     less than that of other instances for FAlgebra, the
     typeclass inference algorithm will loop.
     *)

  Definition WF_FAlgebra (Name T A: Set) (F G : Set -> Set)
    {subfg: F :<: G}
    (falg: FAlgebra Name T A F)
    (galg: FAlgebra Name T A G) : Set :=
      WF_Mixin T A F G subfg
                 (f_algebra (FAlgebra := falg))
                 (f_algebra (FAlgebra := galg)).

  (*
  Class WF_FAlgebra (Name A: Set) (F G: Set -> Set)
    (subfg: F :<: G)
    (falg: FAlgebra Name A F)
    (galg: FAlgebra Name A G): Set :=
    { wf_algebra :
      forall (fa: F A),
        @f_algebra Name A G galg (@inj F G subfg A fa) = @f_algebra Name A F falg fa }.
   *)

  Global Instance WF_FAlgebra_id {Name T A : Set} {F} {falg: FAlgebra Name T A F}:
    WF_Mixin T A F F Sub_Functor_id
      (f_algebra (FAlgebra := falg))
      (f_algebra (FAlgebra := falg)).
  Proof.
    apply WF_Mixin_id.
  Defined.

  Global Instance WF_FAlgebra_inl
    {Name A T : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_G: F :<: G}
    {wf_F_G: WF_FAlgebra Name T A F G falg galg}
    :
    WF_Mixin T A F (G :+: H) (Sub_Functor_inl F G H sub_F_G)
      (f_algebra (FAlgebra := falg))
      (f_algebra (FAlgebra := FAlgebra_Plus Name T A G H)).
  Proof.
    simpl; unfold WF_FAlgebra in wf_F_G; apply WF_Mixin_inl.
  Defined.

  Global Instance WF_FAlgebra_inr
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {wf_G_H: WF_FAlgebra Name T A F H falg halg}
    :
    WF_Mixin T A F (G :+: H) (Sub_Functor_inr F G H sub_F_H)
      (f_algebra (FAlgebra := falg))
      (f_algebra (FAlgebra := FAlgebra_Plus Name T A G H)).
  Proof.
    simpl; unfold WF_FAlgebra in wf_G_H; apply WF_Mixin_inr.
  Defined.

  Class iPAlgebra (Name : Set) {I : Set}
    (A : I -> Prop) (F: (I -> Prop) -> I -> Prop) : Set :=
    { if_algebra : iAlgebra F A }.

  Global Instance iPAlgebra_Plus (Name: Set) {I : Set}
    (A : I -> Prop) (F G : (I -> Prop) -> I -> Prop)
    {falg: iPAlgebra Name A F} {galg: iPAlgebra Name A G} :
    iPAlgebra Name A (F ::+:: G) | 6 :=
    {| if_algebra := iAlgebra_Plus if_algebra if_algebra |}.

End FAlgebra.

Arguments f_algebra _ {_ _ _ _} _ _.

  (* ============================================== *)
  (* INDUCTION PRINCIPLES INFRASTRUCTURE            *)
  (* ============================================== *)

Section PAlgebras.

  Class FPAlgebra {A : Set} (P : A -> Prop)
    {F : Set -> Set} `{PFun_F : PFunctor F} (falg : Algebra F A) :=
    { p_algebra : PAlgebra falg P }.

  Class FPMixin {T A : Set} (P : T -> Prop) (Q : A -> Prop)
    {F : Set -> Set} `{PFun_F : PFunctor F} (f : Mixin T F A) :=
    { p_mixin : PMixin T F f P Q }.

  Instance Sub_Functor_inl' {F G H : Set -> Set} (sub_F_G : (F :+: G) :<: H) :
    F :<: H :=
    {| inj := fun (A : Set) (e : F A) => @inj _ _ sub_F_G A (inl _ e);
       prj := fun (A : Set) (ha : H A) =>
                match @prj _ _ sub_F_G A ha with
                  | Some (inl f) => Some f
                  | Some (inr g) => None
                  | None => None
                end
    |}.
  Proof.
    intros until fa; caseEq (prj ga);
      [rewrite (inj_prj _ _ H0); destruct i; congruence | discriminate].
    intros; rewrite prj_inj; reflexivity.
  Defined.

  Instance Sub_Functor_inr' {F G H : Set -> Set} (sub_F_G : (F :+: G) :<: H) :
    G :<: H :=
    {| inj := fun (A : Set) (e : G A) => (@inj _ _ sub_F_G A (inr _ e));
       prj := fun (A : Set) (H0 : H A) =>
                match @prj _ _ sub_F_G A H0 with
                  | Some (inl f) => None
                  | Some (inr g) => Some g
                  | None => None
                end
    |}.
  Proof.
    intros until fa; caseEq (prj ga);
      [rewrite (inj_prj _ _ H0); destruct i; congruence | discriminate].
    intros; rewrite prj_inj; reflexivity.
  Defined.

  (*
  Global Instance WF_Functor_Sub_Functor_inl'
    (F G H : Set -> Set) (sub_F_G_H : (F :+: G) :<: H)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {WF_sub_F_G_H : WF_Functor _ _ sub_F_G_H _ _ } :
    WF_Functor F H (Sub_Functor_inl' _ _ _ sub_F_G_H) _ _.
  Proof.
    econstructor; intros.
    simpl; erewrite wf_functor; simpl; reflexivity.
  Qed.

  Global Instance WF_Functor_Sub_Functor_inr'
    (F G H : Set -> Set) (sub_F_G_H : (F :+: G) :<: H)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {WF_sub_F_G_H : WF_Functor _ _ sub_F_G_H _ _ } :
    WF_Functor G H (Sub_Functor_inr' _ _ _ sub_F_G_H) _ _.
  Proof.
    econstructor; intros.
    simpl; erewrite wf_functor; simpl; reflexivity.
  Qed.

  Global Instance WF_FAlgebra_inl'
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name A F}
    {galg: FAlgebra Name A G}
    {halg: FAlgebra Name A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name A (F :+: G) H sub_F_G_H (FAlgebra_Plus _ _ F G) halg}
    :
    WF_FAlgebra Name A F H (Sub_Functor_inl' F G H sub_F_G_H)
    falg halg.
  Proof.
    constructor; intros; simpl; rewrite wf_algebra; reflexivity.
  Qed.

  Global Instance WF_FAlgebra_inr'
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name A F}
    {galg: FAlgebra Name A G}
    {halg: FAlgebra Name A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name A (F :+: G) H sub_F_G_H (FAlgebra_Plus _ _ F G) halg}
    :
    WF_FAlgebra Name A G H (Sub_Functor_inr' F G H sub_F_G_H)
    galg halg.
  Proof.
    constructor; intros; simpl; rewrite wf_algebra; reflexivity.
  Qed.
  *)

  Global Instance WF_Mixin_inl'
    {T A : Set}
    {F G H}
    {falg: Mixin T F A}
    {galg: Mixin T G A}
    {halg: Mixin T H A}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_Mixin T A (F :+: G) H sub_F_G_H (Mixin_Plus falg galg) halg}
    :
    WF_Mixin T A F H (Sub_Functor_inl' sub_F_G_H) falg halg.
  Proof.
    constructor; intros; simpl; rewrite wf_mixin; reflexivity.
  Qed.

  Global Instance WF_Mixin_inr'
    {T A : Set}
    {F G H}
    {falg: Mixin T F A}
    {galg: Mixin T G A}
    {halg: Mixin T H A}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_Mixin T A (F :+: G) H sub_F_G_H (Mixin_Plus falg galg) halg}
    :
    WF_Mixin T A G H (Sub_Functor_inr' sub_F_G_H) galg halg.
  Proof.
    constructor; intros; simpl; rewrite wf_mixin; reflexivity.
  Qed.


  Global Instance WF_FAlgebra_inl'
    {Name A T : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name T A (F :+: G) H (FAlgebra_Plus Name T A F G) halg}
    :
    WF_Mixin T A F H (Sub_Functor_inl' sub_F_G_H)
             (f_algebra Name (FAlgebra := falg))
             (f_algebra Name (FAlgebra := halg)).
  Proof.
    unfold WF_FAlgebra in *; apply WF_Mixin_inl'.
  Defined.

  Global Instance WF_FAlgebra_inr'
    {Name A T : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name T A (F :+: G) H (FAlgebra_Plus Name T A F G) halg}
    :
    WF_Mixin T A G H (Sub_Functor_inr' sub_F_G_H)
             (f_algebra Name (FAlgebra := galg))
             (f_algebra Name (FAlgebra := halg)).
  Proof.
    unfold WF_FAlgebra in *; apply WF_Mixin_inr'.
  Defined.

  (*
  Global Instance FPAlgebra_Plus
    (F G : Set -> Set)
    `{PFun_F : PFunctor F}
    `{PFun_G : PFunctor G}
    {A : Set}
    (P : A -> Prop)
    {falg : Algebra F A}
    {galg : Algebra G A}
    {fpalg: FPAlgebra P falg}
    {gpalg: FPAlgebra P galg}
    :
    FPAlgebra P (Algebra_Plus falg galg) | 6 :=
    {| p_algebra := PAlgebra_Plus P p_algebra p_algebra |}.
  *)

  (* The key reasoning lemma. *)
  Lemma Ind {F : Set -> Set} `{spf_F : SPF F}
        {P : Fix F -> Prop} {Ind_Alg : FPAlgebra P in_t} :
    forall (f : Fix F), P f.
  Proof.
    apply ind.
    apply p_algebra.
  Qed.

  Definition inject2 (F G G' : Set -> Set)
    `{PFun_F : Functor F} `{spf_G : SPF G} `{spf_G' : SPF G'}
    {sub_F_G : F :<: G}
    {sub_F_G' : F :<: G'} : Algebra F (Fix G * Fix G') :=
    fun x => (inject _ _ (fmap (fst (B:=Fix G')) x),
              inject _ _ (fmap (snd (B:=Fix G')) x)).

  (*
  Global Instance P2Algebra_Plus {F G H H'}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {Fun_H' : Functor H'}
    {sub_F_G_H : (F :+: G) :<: H}
    {sub_F_G_H' : (F :+: G) :<: H'}
    {Name : Set}
    {P : (Fix H) * (Fix H') -> Prop}
    {falg: @P2Algebra Name F H H' _ _ _ P (Sub_Functor_inl' _ _ _ sub_F_G_H) (Sub_Functor_inl' _ _ _ sub_F_G_H')}
    {galg: @P2Algebra Name G H H' _ _ _ P (Sub_Functor_inr' _ _ _ sub_F_G_H) (Sub_Functor_inr' _ _ _ sub_F_G_H')}
    :
    @P2Algebra Name (F :+: G) H H' _ _ _ P sub_F_G_H sub_F_G_H' :=
    {| p2_algebra := fun fga : (F :+: G) (sig P) =>
      (match fga with
         | inl fa => p2_algebra (P2Algebra := falg) fa
         | inr ga => p2_algebra (P2Algebra := galg) ga
       end) |}.
  Proof.
    intros; destruct e; simpl; rewrite proj1_WF_Ind; simpl; reflexivity.
    intros; destruct e; simpl; rewrite proj2_WF_Ind; simpl; reflexivity.
  Defined.
  *)

  Lemma Ind2 {F : Set -> Set}
    `{spf_F : SPF F}
    {P : (Fix F) * (Fix F) -> Prop}
    {Ind_Alg : FPAlgebra P (inject2 F F F)}
    :
    forall (f : Fix F), P (f, f).
  Proof.
    apply ind with (Q := fun x => P (x, x)).
    intros xs Axs.
    apply All_fmap in Axs.
    generalize (p_algebra (fmap (fun x => (x , x)) xs) Axs).
    unfold inject2, inject; simpl.
    unfold id.
    now rewrite ?fmap_fusion, ?fmap_id.
  Qed.

  (*
  Class iPAlgebra (Name : Set) {I : Set} (A : I -> Prop) (F: (I -> Prop) -> I -> Prop) : Prop :=
    { ip_algebra : iAlgebra F A}.

  (* Definition iPAlgebra_Plus (Name: Set) {I : Set} (A : I -> Prop)
    (F G : (I -> Prop) -> I -> Prop)
    {falg: iPAlgebra Name A F} {galg: iPAlgebra Name A G} :
    iPAlgebra Name A (F ::+:: G) :=
      Build_iPAlgebra Name _ A _
      (fun f fga =>
        (match fga with
           | or_introl fa => ip_algebra f fa
           | or_intror ga => ip_algebra f ga
         end)). *)

  Global Instance iPAlgebra_Plus (Name: Set) {I : Set} (A : I -> Prop)
    (F G : (I -> Prop) -> I -> Prop)
    {falg: iPAlgebra Name A F} {galg: iPAlgebra Name A G} :
    iPAlgebra Name A (F ::+:: G) | 6 :=
    {| ip_algebra := fun f fga =>
                       match fga with
                         | or_introl fa => ip_algebra f fa
                         | or_intror ga => ip_algebra f ga
                       end
    |}.
  *)

End PAlgebras.

(* ============================================== *)
(* ADDTIONAL MENDLER ALGEBRA INFRASTRUCTURE       *)
(* ============================================== *)

Section WF_MAlgebras.

  Class WF_MAlgebra {Name : Set} {F : Set -> Set} {A : Set}
    {Fun_F : Functor F}(MAlg : forall R, FAlgebra Name R A F) :=
    { wf_malgebra :
        forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
          f_algebra Name (FAlgebra := MAlg T) rec (fmap f ft) =
          f_algebra Name (FAlgebra := MAlg T') (fun ft' => rec (f ft')) ft
    }.

  (*
  Global Instance WF_MAlgebra_Plus {Name : Set} {F G : Set -> Set} {A : Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    (MAlg_F : forall R, FAlgebra Name R A F)
    (MAlg_G : forall R, FAlgebra Name R A G)
    {WF_MAlg_F : WF_MAlgebra MAlg_F}
    {WF_MAlg_G : WF_MAlgebra MAlg_G}
    :
    @WF_MAlgebra Name (F :+: G) A _ (fun R => FAlgebra_Plus Name R A F G).
  Proof.
    constructor; intros.
    destruct ft; simpl; apply wf_malgebra.
  Qed.
  *)

End WF_MAlgebras.

Section Isomorphisms.

    Class Iso (F G : Set -> Set) :=
      { toIso                 : forall {A : Set}, G A -> F A;
        fromIso               : forall {A : Set}, F A -> G A;
        toIso_fromIso_inverse : forall {A : Set} (a : F A), toIso (fromIso a) = a;
        fromIso_toIso_inverse : forall {A : Set} (a : G A), fromIso (toIso a) = a
      }.

End Isomorphisms.

Definition Smarked (S: Set) : Set := S.

Ltac Smark H :=
  let t := type of H in
  let n:= fresh in
    (assert (n:Smarked t); [exact H | clear H; rename n into H]).

Ltac unSmark H := unfold Smarked in H.

Ltac unSmark_all := unfold Smarked in *|-.
(*
Ltac WF_Falg_rewrite' :=
  match goal with
    | H : WF_FAlgebra _ _ _ _ _ _ _ |- _ =>
      try rewrite (wf_algebra (WF_FAlgebra := H)); Smark H; WF_Falg_rewrite'
    | _ => simpl
  end;
  unSmark_all.
*)
Hint Extern 0 (FAlgebra _ _ _ (_ :+: _)) =>
  apply FAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (forall _, FAlgebra _ _ _ _) =>
  intros; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (forall _, PAlgebra _ _ _ _) =>
  intros; eauto with typeclass_instances : typeclass_instances.

(*
Hint Extern 0 (PAlgebra _ (_ :+: _) _ _) =>
  apply PAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.
*)

Hint Extern 0 (iPAlgebra _ _ (_ :+: _)) =>
  apply iPAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (WF_MAlgebra _) =>
  let T := fresh in
    let T' := fresh in
      let f' := fresh in
        let rec' := fresh in
          let ft := fresh in
            constructor; intros T T' f' rec' ft; destruct ft;
              simpl; auto; fail : typeclass_instances.

Hint Extern 0 (WF_FAlgebra _ _ _ _ _ _ _) =>
  unfold WF_FAlgebra; simpl : typeclass_instances.

Hint Extern 0 (FPAlgebra _ in_t) =>
  rewrite <- inject_in_t; eauto with typeclass_instances : typeclass_instances.

Ltac discriminate_inject H :=
  first [ apply inj_prj in H | idtac ];
    contradict H;
      solve [ apply inject_discriminate; auto with typeclass_instances
            | apply not_eq_sym; apply inject_discriminate; auto with typeclass_instances
            | apply inj_discriminate; auto with typeclass_instances
            | apply not_eq_sym; apply inj_discriminate; auto with typeclass_instances
            ].

Ltac project_discriminate :=
  match goal with
    | [ H : @project _ _ _ _ _ _ _ = Some _ |- _ ] =>
      apply inject_project in H; discriminate_inject H
  end.

Ltac crush_project :=
  intros;
    match goal with
      | [ |- context [ @project _ _ _ _ _ ?sub ?x ] ] =>
        caseEq (@project _ _ _ _ _ sub x);
          solve [ project_discriminate | auto; reflexivity ]
    end.
