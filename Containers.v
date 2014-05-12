
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.

Require Import FunctionalExtensionality.
Require Import Functors.
Require Import FJ_tactics.
Require Import Sum.

Section UnaryContainer.

  (* UNARY CONTAINERS
   *
   * A unary container is given by a type of shapes S and a S-indexed
   * family of position types P. Containers capture the category of
   * stricty positive functors full and faithfully. By using containers
   * we can semantically define the fixed point of any strictly positive
   * functor, i.e. capture every strictly positive type.
   *
   *)
  Variable S : Set.
  Variable P : S -> Set.

  (* The extension of a container is a functor. For any type A an element
     of (Ext A) is a dependent pair (s , pf) where (s : S) is a shape and
     (pf : P s -> A) is a function assigning an element of A to every
     position of the shape s.
   *)
  Inductive Ext (A : Set) : Set :=
  | ext: forall (s : S) (pf : P s -> A), Ext A.

  Global Arguments ext [A] s pf.

  Definition gmap {A B : Set} (f : A -> B) (x : Ext A) : Ext B :=
    match x with
    | ext s pf => ext s (fun x => f (pf x))
    end.

  Lemma gmap_fusion {A B D : Set} (f : A -> B) (g : B -> D) (a : Ext A) :
    gmap g (gmap f a) = gmap (fun e => g (f e)) a.
  Proof.
    destruct a.
    reflexivity.
  Qed.

  Lemma gmap_reflection {A : Set} (a : Ext A) :
    gmap (fun x => x) a = a.
  Proof.
    destruct a.
    unfold gmap.
    try rewrite <- eta_expansion.
    reflexivity.
  Qed.

  Lemma gmap_reflection' {A : Set} (f : A -> A) :
    (forall a, f a = a) -> (forall a, gmap f a = a).
  Proof.
    intros H x.
    cut (f = id); intros; subst.
    apply gmap_reflection.
    apply functional_extensionality.
    assumption.
  Qed.

  (* A generic all Modality
   *
   * Informally, the GAll modality is, for a predicate (Q : A -> Prop)
   * on (A : Set) a new type that says that Q holds for each (a : A)
   * in an (Ext A).
   *
   *)
  Definition GAll {A : Set} (Q : A -> Prop) : forall (x : Ext A), Prop :=
    fun x =>
      match x with
        | ext s pf => forall (p : P s), Q (pf p)
      end.

  Definition GAll_natural1 {A B : Set} (f : A -> B) (Q : B -> Prop) (xs : Ext A) :
    GAll (fun x => Q (f x)) xs -> GAll Q (gmap f xs).
  Proof.
    destruct xs; auto.
  Qed.

  Definition GAll_natural2 {A B : Set} (f : A -> B) (Q : B -> Prop) (xs : Ext A) :
    GAll Q (gmap f xs) -> GAll (fun x => Q (f x)) xs.
  Proof.
    destruct xs; auto.
  Qed.

  Definition gall {A : Set} {Q : A -> Prop}
             (f : forall (a : A), Q a) (x : Ext A) : GAll Q x :=
    match x with
      | ext s pf => fun p => f (pf p)
    end.

  Inductive W : Set :=
  | sup : forall e : Ext W, W.

  Definition unsup : W -> Ext W :=
    fun x => match x with
               | sup e => e
             end.

  Definition GAlgebra (A : Set) : Set :=
    Ext A -> A.

  Fixpoint gfold {A : Set} (f : GAlgebra A) (x : W) : A :=
    match x with
      | sup (ext s p) => f (ext s (fun x => gfold f (p x)))
    end.

  Lemma gfold_computation (A : Set) (f : GAlgebra A) (a : Ext W) :
    gfold f (sup a) = f (gmap (gfold f) a).
  Proof.
    destruct a; reflexivity.
  Qed.

  Fixpoint gfold_uniqueness
           {A : Set} (f : GAlgebra A) (h : W -> A)
           (H : forall e : Ext W, h (sup e) = f (gmap h e))
           (x : W) : h x = gfold f x.
  Proof.
    destruct x.
    rewrite H.
    destruct e.
    simpl.
    apply f_equal.
    apply f_equal.
    extensionality x.
    apply (gfold_uniqueness A f h H).
  Qed.

  Lemma gfold_reflection (x : W) : gfold sup x = x.
  Proof.
    apply sym_eq.
    apply (gfold_uniqueness sup (fun x => x)).
    intros.
    rewrite gmap_reflection.
    reflexivity.
  Qed.

  Definition GPAlgebra {A : Set} (f : GAlgebra A) (Q : A -> Prop) : Set :=
    forall xs : Ext A, GAll Q xs -> Q (f xs).

  (* A generic induction principle. *)
  Fixpoint gind {Q : W -> Prop} (step : GPAlgebra sup Q) (x : W) : Q x :=
    match x return (Q x) with
      | sup (ext s pf) =>
        step (ext s pf) (fun p : P s => gind step (pf p))
    end.

  Fixpoint gfoldp {A : Set} {f : GAlgebra A} {Q : A -> Prop}
    (step : GPAlgebra f Q) (x : W) : Q (gfold f x) :=
    match x return (Q (gfold f x)) with
      | sup (ext s pf) =>
        step (ext s (fun p : P s => gfold f (pf p)))
             (fun p : P s => gfoldp step (pf p))
    end.

  Corollary gind' {Q : W -> Prop} (step : GPAlgebra sup Q) (x : W) : Q x.
  Proof.
    rewrite <- gfold_reflection.
    apply (gfoldp step).
  Qed.

  Corollary gfoldp' {A : Set} {f : GAlgebra A} {Q : A -> Prop}
    (step : GPAlgebra f Q) (x : W) : Q (gfold f x).
  Proof.
    apply (gind (Q := fun x => Q (gfold f x))).
    intros xs H.
    rewrite gfold_computation.
    apply step.
    apply GAll_natural1.
    assumption.
  Qed.

  Definition GAny {A : Set} (Q : A -> Prop) : forall (x : Ext A), Prop :=
    fun x =>
      match x with
        | ext s pf => exists (p : P s), Q (pf p)
      end.

  Section DependentEquality.

    Lemma eq_dep_eq_ext {A : Set} :
      forall (s s' : S) (p : P s -> A) (p' : P s' -> A),
        eq_dep S (fun s => P s -> A) s p s' p' -> ext s p = ext s' p'.
    Proof.
      intros; destruct H; reflexivity.
    Qed.

  End DependentEquality.

  Definition sh {A : Set} (x : Ext A) : S :=
    match x with
      | ext s pf => s
    end.

  Definition pos {A : Set} (x : Ext A) : P (sh x) -> A :=
    match x with
      | ext s pf => pf
    end.

End UnaryContainer.

Section ContainerClass.

  Class Container (F : Set -> Set) :=
    { Shape           : Set;
      Position        : Shape -> Set;
      to              : forall {A : Set}, Ext Shape Position A -> F A;
      from            : forall {A : Set}, F A -> Ext Shape Position A;
      to_from_inverse : forall {A : Set} (a : F A), to (from a) = a;
      from_to_inverse : forall {A : Set} (a : Ext Shape Position A), from (to a) = a
    }.

  Section Instances.
    Variable F : Set -> Set.
    Context {cont_F : Container F}.

    Global Instance ContainerFunctor : Functor F :=
      {| fmap := fun A B f x => to (gmap Shape Position f (from x)) |}.
    Proof.
      (* fmap_fusion *)
      intros.
      rewrite from_to_inverse.
      rewrite gmap_fusion.
      reflexivity.
      (* fmap_id *)
      intros.
      rewrite gmap_reflection.
      apply to_from_inverse.
    Defined.

    Global Instance ContainerPFunctor :
      PFunctor F := {| All := fun A Q x => GAll Shape Position Q (from x) |}.
    Proof.
      intros.
      unfold GAll; simpl.
      rewrite from_to_inverse.
      destruct (from xs).
      apply H.
    Defined.

    Global Instance ContainerSPF :
      SPF F := {| Fix   := W Shape Position;
                  in_t  := fun x     => sup _ _ (from x);
                  out_t := fun x     => to (unsup _ _ x);
                  fold_ := fun A alg => gfold Shape Position (fun x => alg (to x))
               |}.
    Proof.
      (* foldp *)
      intros.
      apply gfoldp.
      intros e Hall.
      apply H.
      simpl.
      rewrite from_to_inverse.
      apply Hall.
      (* in_out_inverse *)
      intros.
      rewrite from_to_inverse.
      destruct e; reflexivity.
      (* out_in_inverse *)
      intros.
      apply to_from_inverse.
      (* fold_uniqueness *)
      intros.
      apply (gfold_uniqueness Shape Position (fun x => f (to x))).
      intros.
      rewrite <- (from_to_inverse e) at 1.
      rewrite H.
      destruct e; simpl.
      rewrite from_to_inverse.
      reflexivity.
      (* fold_computation *)
      intros.
      apply (gfold_computation Shape Position A (fun x => f (to x))).
    Defined.
  End Instances.

  Section Constant.

    Variable X : Set.
    Variable H : Set -> Set.

    Inductive ConstS := SConst : X -> ConstS.
    Inductive ConstP : ConstS -> Set :=.

    Variable (toX    : forall A, H A -> X).
    Variable (fromX  : forall A, X -> H A).
    Variable (toFrom : forall A (x : X), toX A (fromX A x) = x).
    Variable (fromTo : forall A (x : H A), fromX _ (toX _ x) = x).

    Instance ConstContainer : Container H :=
      {|
        Shape    := ConstS;
        Position := ConstP;
        to       := fun A x =>
                      match x with
                        | ext s pf =>
                          match s return (ConstP s -> A) -> H A with
                            | SConst x => fun _ => fromX A x
                          end pf
                      end;
        from     := fun A x =>
                      ext ConstS ConstP
                          (SConst (toX A x))
                          (fun p => match p in ConstP _
                                    with end)
                          |}.
    Proof.
      (* from_to_inverse *)
      intros; simpl; rewrite fromTo; reflexivity.
      (* to_from_inverse *)
      destruct a as [[s] pf]; simpl.
      rewrite toFrom.
      apply f_equal.
      extensionality p.
      dependent destruction p.
    Defined.

  End Constant.

  Section Combinators.

    Section Isomorphism.

      Instance ContainerIso {F G : Set -> Set} {cont_G : Container G}
        (iso_FG : Iso F G) : Container F :=
        {| Shape := @Shape G _;
           Position := @Position G _;
           to := fun A x => toIso (to x);
           from := fun A x => from (fromIso x)
        |}.
      Proof.
        intros; rewrite to_from_inverse, toIso_fromIso_inverse; auto.
        intros; rewrite fromIso_toIso_inverse, from_to_inverse; auto.
      Defined.

    End Isomorphism.

    Section Identity.

      Definition Id (A : Set) : Set := A.

      Global Instance ContainerId : Container Id.
        refine ({| Shape := unit;
                   Position := fun s => unit;
                   to := fun A x => match x with
                                      | ext s pf => pf tt
                                    end;
                   from := fun A x => ext unit (fun s => unit) tt (fun p => x)
        |}).
        reflexivity.
        intros.
        destruct a as [[] pf].
        f_equal.
        extensionality p.
        destruct p.
        reflexivity.
      Defined.

      Global Opaque Id.

    End Identity.

    Section Constants.

      Definition K (X : Set) (A : Set) : Set := X.

      Global Instance ContainerK (X : Set) : Container (K X) :=
        ConstContainer X (K X)
          (fun A ka => ka)
          (fun A ka => ka)
          (fun A x => eq_refl)
          (fun A x => eq_refl).

      Global Opaque K.

    End Constants.

    Section Sums.

      Variable F : Set -> Set.
      Context {cont_F : Container F}.

      Variable G : Set -> Set.
      Context {cont_G : Container G}.

      Definition SumS : Set        := sum (@Shape F _) (@Shape G _).
      Definition SumP : SumS -> Set := fold_sum (@Position F _) (@Position G _).

      Definition fromSum (A : Set) (x : (F :+: G) A) : Ext SumS SumP A :=
        match x with
          | inl y => match from y with
                       | ext s p => ext _ _ (inl _ s) p
                     end
          | inr y => match from y with
                       | ext s p => ext _ _ (inr _ s) p
                     end
        end.

      Definition toSum (A : Set) (x : Ext SumS SumP A) : (F :+: G) A :=
        match x with
          | ext s pf =>
          match s return ((SumP s -> A) -> (F :+: G) A)
          with
            | inl s => fun pf => inl _ (to (ext _ _ s pf))
            | inr s => fun pf => inr _ (to (ext _ _ s pf))
          end pf
      end.

      Global Instance ContainerSum : Container (F :+: G) | 6 :=
      {| Shape    := SumS;
         Position := SumP;
         from     := fromSum;
         to       := toSum |}.
      Proof.
        (* to_from *)
        intros.
        destruct a as [x|x];
          simpl;
          remember (from x);
          destruct e; simpl;
          rewrite Heqe;
          rewrite to_from_inverse;
          reflexivity.
        (* from_to *)
        intros.
        destruct a as [[s|s] pf];
          simpl;
          rewrite from_to_inverse;
          reflexivity.
      Defined.

    End Sums.

    Section Products.

      Variable F : Set -> Set.
      Context {cont_F : Container F}.

      Variable G : Set -> Set.
      Context {cont_G : Container G}.

      Definition ProdS : Set          := (@Shape F cont_F * @Shape G cont_G)%type.
      Definition ProdP : ProdS -> Set :=
        fun s =>
          match s with
            | (s1, s2) => (Position s1) + (Position s2)
          end%type.

      Definition fromProd (A : Set) (x : (F :*: G) A) : Ext ProdS ProdP A :=
        match x with
          | (f, g) => match from f , from g with
                        | ext s1 pf1 , ext s2 pf2 => ext _ _ (s1 , s2) (fold_sum' pf1 pf2)
                      end
        end.

      Definition toProd (A : Set) (x : Ext ProdS ProdP A) : (F :*: G) A :=
        match x in Ext _ _ _ with
          | ext (s1, s2) pf =>
            (to (ext _ _ s1 (fun p => pf (inl p))),
             to (ext _ _ s2 (fun p => pf (inr p))))
        end.

      Global Instance ContainerProd : Container (F :*: G) :=
      {| Shape    := ProdS;
         Position := ProdP;
         from     := fromProd;
         to       := toProd
      |}.
      Proof.
        (* to_from *)
        destruct a as [f g]; simpl.
        caseEq (from f); caseEq (from g); simpl.
        rewrite <- (eta_expansion pf), <- (eta_expansion pf0).
        rewrite <- H, <- H0.
        repeat rewrite to_from_inverse.
        reflexivity.
        (* from_to *)
        destruct a; destruct s; simpl.
        repeat rewrite from_to_inverse.
        f_equal; extensionality p; destruct p; reflexivity.
      Defined.

    End Products.

    Section Lists.

      Inductive Fin : nat -> Set :=
      | f0  : forall {n}, Fin (S n)
      | fS  : forall {n}, Fin n -> Fin (S n).

      Definition nofin {A : Set} (i : Fin 0) : A :=
        match match i in Fin k
                    return match k return Type with
                             | O => Empty_set
                             | S n => unit
                           end
              with
                | f0 _ => tt
                | fS _ _ => tt
              end
        with
        end.

      Definition caseFin {A} {n} (a : A) (pf : Fin n -> A) (i : Fin (S n)) : A :=
        match i in Fin k
              return match k return Type with
                       | O    => Empty_set
                       | S n' => (Fin n' -> A) -> A
                     end
        with
          | f0 _   => fun _  => a
          | fS _ j => fun pf => pf j
        end pf.

      Definition nil' {A : Set} : Ext nat Fin A := ext nat Fin 0 nofin.

      Definition cons' {A : Set} (x : A) (xs : Ext nat Fin A) : Ext nat Fin A :=
        match xs with
          | ext s pf => ext nat Fin (S s) (caseFin x pf)
        end.

      Fixpoint tabulate {A : Set} {n : nat} : (Fin n -> A) -> list A :=
        match n return (Fin n -> A) -> list A with
          | O   => fun f => nil
          | S n => fun f => cons (f f0) (tabulate (fun x => f (fS x)))
        end.

      Definition toList (A : Set) (xs : Ext nat Fin A) : list A :=
        match xs with
          | ext s pf => tabulate pf
        end.

      Fixpoint fromList (A : Set) (xs : list A) : Ext nat Fin A :=
        match xs with
          | nil => nil'
          | cons x xs => cons' x (fromList A xs)
        end.

      Global Instance ContainerList : Container list :=
      {| Shape    := nat;
         Position := Fin;
         from     := fromList;
         to       := toList |}.
      Proof.
        (* to_from_inverse *)
        induction a.
        reflexivity.
        rewrite <- IHa at 2.
        unfold toList.
        simpl.
        destruct (fromList A a0).
        reflexivity.
        (* from_to_inverse *)
        destruct a.
        induction s.
        simpl.
        unfold nil'.
        apply f_equal.
        extensionality x.
        inversion x.
        simpl in IHs.
        simpl.
        rewrite IHs.
        simpl.
        apply f_equal.
        extensionality p.
        dependent destruction p; reflexivity.
      Defined.

    End Lists.

    Section Comp.

      Variable F : Set -> Set.
      Variable G : Set -> Set.
      Context {cont_F : Container F}.
      Context {cont_G : Container G}.

      Let S1 := @Shape F _.
      Let P1 := @Position F _.

      Let S2 := @Shape G _.
      Let P2 := @Position G _.

      Definition Comp (A : Set) := F (G A).
      Definition CompS := Ext S1 P1 S2.
      Definition CompP (s : CompS) := {p : P1 (sh S1 P1 s) & P2 (pos S1 P1 s p)}.

      Definition fromExts {A : Set} (x : Ext S1 P1 (Ext S2 P2 A)) : Ext CompS CompP A :=
        match x with
          | ext s pf =>
            ext _ _
                (ext _ _ s (fun p => sh _ _ (pf p)))
                (fun p : {p1 : P1 s & P2 (sh S2 P2 (pf p1))} =>
                   pos S2 P2 (pf (projT1 p)) (projT2 p))
        end.

      Definition toExts {A : Set} (x : Ext CompS CompP A) : Ext S1 P1 (Ext S2 P2 A) :=
        match x with
          | ext s pf =>
            ext S1 P1 (sh S1 P1 s) (fun p1 =>
              ext S2 P2 (pos S1 P1 s p1) (fun p2 =>
                pf (existT (fun p => P2 (pos S1 P1 s p)) p1 p2)))
        end.

      Lemma fromExts_toExts (A : Set) (x : Ext CompS CompP A) :
        fromExts (toExts x) = x.
      Proof.
        destruct x as [[s1 pf1] pf].
        simpl in *.
        f_equal.
        extensionality p.
        destruct p; reflexivity.
      Defined.

      Lemma toExts_fromExts (A : Set) (x : Ext S1 P1 (Ext S2 P2 A)) :
        toExts (fromExts x) = x.
      Proof.
        destruct x as [s1 pf1].
        simpl in *.
        f_equal.
        extensionality p.
        destruct (pf1 p).
        reflexivity.
      Defined.

      Definition fromComp (A : Set) (x : Comp A) : Ext CompS CompP A :=
        fromExts (gmap S1 P1 from (from (Container := cont_F) x)).

      Definition toComp (A : Set) (x : Ext CompS CompP A) : Comp A :=
        to (gmap S1 P1 to (toExts x)).

      (* The priority of composition has to be low enough (i.e. lower than
         coproducts) to make real progress first before trying senseless
         instances like compositions with the identity container.
      *)
      Global Instance ContainerComp : Container (fun A => F (G A)) | 20 :=
      {| Shape    := CompS;
         Position := CompP;
         from     := fromComp;
         to       := toComp
      |}.
      Proof.
        (* to_from_inverse *)
        intros A x.
        unfold toComp, fromComp.
        rewrite toExts_fromExts.
        rewrite gmap_fusion.
        rewrite <- (to_from_inverse x) at 2.
        f_equal.
        apply gmap_reflection'.
        apply to_from_inverse.
        (* from_to_inverse *)
        intros A x.
        unfold toComp, fromComp.
        rewrite from_to_inverse.
        rewrite gmap_fusion.
        rewrite gmap_reflection'.
        apply fromExts_toExts.
        apply from_to_inverse.
      Defined.

    End Comp.

    Section Exponentials.

      Definition Fn (X : Set) (A : Set) : Set := X -> A.

      Global Instance ContainerFn (X : Set) : Container (Fn X) :=
        {| Shape    := unit;
           Position := fun s => X;
           from     := fun A f => ext unit (fun s => X) tt f;
           to       := fun A x =>
                         match x with
                           | ext _ f => f
                         end
        |}.
      Proof.
        auto.
        intros; destruct a as [[] f]; auto.
      Defined.

      Global Opaque Fn.

    End Exponentials.

  End Combinators.

  Section WellFormedFunctor.

    Global Instance WF_Functor_plus_cont_inl
      {F G H : Set -> Set}
      {Fun_F : Functor F}
      {Cont_G : Container G}
      {Cont_H : Container H}
      {Sub_FG : F :<: G}
      {WF_Fun_F : WF_Functor F _ Sub_FG}
      :
      WF_Functor F (G :+: H) (Sub_Functor_inl F G H _ ) (Fun_G := ContainerFunctor (G :+: H)) | 6.
    Proof.
      constructor; simpl; intros.
      rewrite <- wf_functor.
      simpl.
      destruct (from (inj fa)).
      reflexivity.
    Defined.

    Global Instance WF_Functor_plus_cont_inr
      {F G H : Set -> Set}
      {Fun_F : Functor F}
      {Cont_G : Container G}
      {Cont_H : Container H}
      {Sub_FH : F :<: H}
      {WF_Fun_F : WF_Functor F _ Sub_FH}
      :
      WF_Functor F (G :+: H) (Sub_Functor_inr F G H _ ) (Fun_G := ContainerFunctor (G :+: H)) | 6.
    Proof.
      constructor; simpl; intros.
      rewrite <- wf_functor.
      simpl.
      destruct (from (inj fa)).
      reflexivity.
    Defined.

    Global Instance WF_Functor_plus_cont_inl'
      {F G H : Set -> Set}
      {Cont_F : Container F}
      {Cont_G : Container G}
      {Fun_H : Functor H}
      {sub_FG_H : (F :+: G) :<: H}
      {WF_Fun_FG_H : WF_Functor _ _ sub_FG_H (Fun_F := ContainerFunctor (F :+: G))}
      :
      WF_Functor _ _ (Sub_Functor_inl' sub_FG_H) | 6.
    Proof.
      constructor; intros.
      simpl (inj fa).
      rewrite wf_functor.
      simpl.
      destruct (from fa).
      reflexivity.
    Defined.

    Global Instance WF_Functor_plus_cont_inr'
      {F G H : Set -> Set}
      {Cont_F : Container F}
      {Cont_G : Container G}
      {Fun_H : Functor H}
      {sub_FG_H : (F :+: G) :<: H}
      {WF_Fun_FG_H : WF_Functor _ _ sub_FG_H (Fun_F := ContainerFunctor (F :+: G))}
      :
      WF_Functor _ _ (Sub_Functor_inr' sub_FG_H) | 6.
    Proof.
      constructor; intros.
      simpl (inj fa).
      rewrite wf_functor.
      simpl.
      destruct (from fa).
      reflexivity.
    Defined.

  End WellFormedFunctor.

  Section Algebras.

    Variable F : Set -> Set.
    Context {cont_F : Container F}.

    Variable G : Set -> Set.
    Context {cont_G : Container G}.

    Lemma PAlgebra_Plus_cont {A : Set} {falg : Algebra F A} {galg : Algebra G A}
          (Q : A -> Prop) (fpalg : PAlgebra falg Q) (gpalg : PAlgebra galg Q) :
      PAlgebra (Algebra_Plus falg galg) Q.
    Proof.
      intro xs;
        destruct xs as [x|x]; simpl;
        intro IH; first [apply fpalg | apply gpalg]; simpl;
        remember (from x) as e; destruct e; apply IH.
    Defined.

    Global Instance FPAlgebra_Plus_cont
      {A : Set}
      (P : A -> Prop)
      {falg : Algebra F A}
      {galg : Algebra G A}
      {fpalg: FPAlgebra P falg}
      {gpalg: FPAlgebra P galg}
      :
      FPAlgebra P (Algebra_Plus falg galg) | 6 :=
      {| p_algebra := PAlgebra_Plus_cont P p_algebra p_algebra |}.


    Global Instance FPAlgebra_Plus_cont_inject
      (H : Set -> Set) `{spf_H : SPF H} (sub_FG_H : (F :+: G) :<: H)
      (P : Fix (F := H) -> Prop)
      {fpalg: FPAlgebra P (inject' (subGF := Sub_Functor_inl' sub_FG_H) F)}
      {gpalg: FPAlgebra P (inject' (subGF := Sub_Functor_inr' sub_FG_H) G)}
      :
      FPAlgebra P (inject' (F :+: G)) | 6.
    Proof.
      assert (inject' (F := H) (F :+: G) =
              Algebra_Plus
                (inject' (subGF := Sub_Functor_inl' sub_FG_H) F)
                (inject' (subGF := Sub_Functor_inr' sub_FG_H) G)).
      extensionality x; destruct x; reflexivity; auto.
      rewrite H0.
      apply FPAlgebra_Plus_cont; auto.
    Defined.

    Global Instance FPAlgebra_Plus_cont_inject2
      (H H' : Set -> Set) `{spf_H : SPF H} `{spf_H' : SPF H'}
      (sub_FG_H : (F :+: G) :<: H)
      (sub_FG_H' : (F :+: G) :<: H')
      {WF_FG_H : WF_Functor _ _ sub_FG_H}
      {WF_FG_H' : WF_Functor _ _ sub_FG_H'}
      (P : (Fix (F := H) * Fix (F := H')) -> Prop)
      {fpalg: FPAlgebra P (inject2 (sub_F_G := Sub_Functor_inl' sub_FG_H) (sub_F_G' := Sub_Functor_inl' sub_FG_H'))}
      {gpalg: FPAlgebra P (inject2 (sub_F_G := Sub_Functor_inr' sub_FG_H) (sub_F_G' := Sub_Functor_inr' sub_FG_H'))}
      :
      FPAlgebra P (inject2 (F := F :+: G)) | 6.
    Proof.
      assert (inject2 (sub_F_G := sub_FG_H) (sub_F_G' := sub_FG_H') =
              Algebra_Plus
                (inject2 (sub_F_G := Sub_Functor_inl' sub_FG_H) (sub_F_G' := Sub_Functor_inl' sub_FG_H'))
                (inject2 (sub_F_G := Sub_Functor_inr' sub_FG_H) (sub_F_G' := Sub_Functor_inr' sub_FG_H'))).
      extensionality x; unfold inject2, inject, Algebra_Plus.
      destruct x; repeat rewrite <- wf_functor; reflexivity.
      rewrite H0.
      apply FPAlgebra_Plus_cont; auto.
    Defined.

    Global Instance WF_MAlgebra_Plus_cont {Name : Set} {A : Set}
           (MAlg_F : forall R, FAlgebra Name R A F)
           (MAlg_G : forall R, FAlgebra Name R A G)
           {WF_MAlg_F : WF_MAlgebra MAlg_F}
           {WF_MAlg_G : WF_MAlgebra MAlg_G}
    :
      @WF_MAlgebra Name (F :+: G) A _ (fun R => FAlgebra_Plus Name R A F G) | 6.
    Proof.
      constructor; intros.
      destruct ft; simpl.
      generalize (wf_malgebra (WF_MAlgebra := WF_MAlg_F) T T' f rec f1).
      simpl; unfold fmap; caseEq (from f1); apply H0.
      generalize (wf_malgebra (WF_MAlgebra := WF_MAlg_G) T T' f rec g).
      simpl; unfold fmap; caseEq (from g); apply H0.
    Defined.

  End Algebras.

End ContainerClass.

Section Indexed.

  Variable I : Set.

  Definition Fam := I -> Prop.

  Variable S : I -> Type.
  Variable P : forall {i : I}, S i -> Type.
  Variable R : forall {i : I} {s : S i}, P i s -> I.

  Global Implicit Arguments P [[i]].
  Global Implicit Arguments R [[i] [s]].

  Inductive IExt (A : Fam) (i : I) : Prop :=
  | iext: forall (s : S i) (pf : forall p : P s, A (R p)), IExt A i.

  Implicit Arguments iext [[A] [i]].

  Definition igfmap
             {A B : Fam} (f : forall i : I, A i -> B i)
             (i : I) (x : IExt A i) : IExt B i :=
    match x with
      | iext s pf => iext s (fun x => f _ (pf x))
    end.

  Lemma igfmap_fusion
        {A B D : Fam}
        (f : forall (i : I), A i -> B i)
        (g : forall (i : I), B i -> D i)
        (i : I) (x : IExt A i) :
    igfmap g i (igfmap f i x) = igfmap (fun i e => g i (f i e)) i x.
  Proof.
    destruct x.
    reflexivity.
  Qed.

  Lemma igfmap_id {A : Fam} (i : I) (a : IExt A i) :
    igfmap (fun i x => x) i a = a.
  Proof.
    destruct a.
    unfold igfmap.
    try rewrite <- eta_expansion_dep.
    reflexivity.
  Qed.

  Inductive IW (i : I) : Prop :=
  | isup : forall e : IExt IW i, IW i.

  Definition ICAlgebra (A : Fam) : Set :=
    forall (i : I), IExt A i -> A i.

  Fixpoint igfold {A : Fam} (f : ICAlgebra A) (i : I) (x : IW i) : A i :=
    match x with
      | isup (iext s p) => f _ (iext s (fun x => igfold f _ (p x)))
    end.

  Lemma igfold_universal_exist (A : Fam) (f : ICAlgebra A)
        (i : I) (x : IExt IW i) :
    igfold f _ (isup _ x) = f _ (igfmap (igfold f) _ x).
  Proof.
    destruct x; reflexivity.
  Qed.

  Fixpoint igfold_universal_unique
           {A : Fam} (f : ICAlgebra A) (h : forall i : I, IW i -> A i)
           (H : forall (i : I) (e : IExt IW i), h _ (isup _ e) = f _ (igfmap h _ e))
           (i : I) (x : IW i) : h _ x = igfold f _ x.
  Proof.
    destruct x.
    rewrite H.
    destruct e.
    unfold igfold.
    simpl.
    apply f_equal.
    apply f_equal.
    extensionality x.
    apply (igfold_universal_unique A f h H).
  Qed.

End Indexed.

Implicit Arguments IExt [[I]].
Implicit Arguments iext [[S] [P] [R] [A]].
Implicit Arguments IW [[I]].

Section IndexedClass.

  Class IContainer {I : Set} (F : (I -> Prop) -> I -> Prop) :=
    { IS                : I -> Type;
      IP                : forall (i : I), IS i -> Type;
      IR                : forall (i : I) (s : IS i), IP i s -> I;
      ito               : forall {A : Fam I} {i : I}, IExt IS IP IR A i -> F A i;
      ifrom             : forall {A : Fam I} {i : I}, F A i -> IExt IS IP IR A i;
      ito_ifrom_inverse : forall {A : Fam I} {i : I} (a : F A i), ito (ifrom a) = a;
      ifrom_ito_inverse : forall {A : Fam I} {i : I} (a : IExt IS IP IR A i), ifrom (ito a) = a
    }.

  Section Instances.
    Variable I : Set.
    Variable F : (I -> Prop) -> I -> Prop.
    Context {icont_F : IContainer F}.

    Definition IAlgebra {I : Set} (F: Fam I -> Fam I) (A : Fam I) :=
      forall i : I, F A i -> A i.

    Definition IFix : Fam I := IW IS IP IR.

    Definition ifmap {A B : Fam I} (f : forall i : I, A i -> B i)
                     (i : I) (x : F A i) : F B i:=
      ito (igfmap I IS IP IR f i (ifrom x)).


    Global Instance IContainerFunctor : iFunctor F :=
      {| ifmap := fun A B i f x => ito (igfmap I IS IP IR f i (ifrom x)) |}.
    Proof.
      (* ifmap_fusion *)
      intros.
      rewrite ifrom_ito_inverse.
      rewrite igfmap_fusion.
      reflexivity.
      (* fmap_id *)
      intros.
      rewrite igfmap_id.
      apply ito_ifrom_inverse.
    Defined.

    Global Instance IContainerSPF :
      iSPF F := {| iFix   := IW IS IP IR;
                   in_ti  := fun i x     => @isup I IS IP IR i (ifrom x);
                   out_ti := fun i x     => match x with isup y => ito y end;
                   ifold_ := fun A alg i => igfold I IS IP IR (fun i x => alg i (ito x)) i
                |}.
    Proof.
      destruct e; f_equal.
      apply ifrom_ito_inverse.
      intros.
      apply ito_ifrom_inverse.
    Defined.

    (*
    Lemma ifold_universal_exist
          {A : Fam I} (f : IAlgebra F A) (i : I) (a : F IFix i) :
      ifold_ f i (in_ti a) = f i (ifmap (ifold_ f) i a).
    Proof.
      apply (igfold_universal_exist I IS IP IR A (fun i x => f i (ito x))).
    Qed.

    Lemma ifold_universal_unique
          {A : Fam I} (f : IAlgebra F A) :
      forall (h : forall i : I, IFix i -> A i)
             (H : forall (i : I) (e : F IFix i), h i (in_ti e) = f i (ifmap h i e))
             (i : I) (x : IFix i), h i x = ifold_ f i x.
    Proof.
      intros h H i x.
      apply igfold_universal_unique.
      intros i' e.
      rewrite <- (ifrom_ito_inverse e).
      apply H.
    Qed.
    *)
  End Instances.

  Section Sums.
    Variable I : Set.
    Variable F : (I -> Prop) -> I -> Prop.
    Context {icont_F : IContainer F}.
    Variable G : (I -> Prop) -> I -> Prop.
    Context {icont_G : IContainer G}.

    Definition ISumS (i : I) : Type         := sum (@IS I F icont_F i) (@IS I G icont_G i).
    Definition ISumP (i : I) : ISumS i -> Type := fold_sum (@IP I F icont_F i) (@IP I G icont_G i).
    Definition ISumR (i : I) (s : ISumS i) : ISumP i s -> I :=
      match s return ISumP i s -> I with
       | inl s0 => @IR I F icont_F i s0
       | inr s0 => @IR I G icont_G i s0
      end.


    Definition ifromSum (A : I -> Prop) (i : I) (x : (F ::+:: G) A i) : IExt ISumS ISumP ISumR A i.
      destruct x; destruct (ifrom H).
      constructor 1 with (s := inl _ s); apply pf.
      constructor 1 with (s := inr _ s); apply pf.
    Defined.

    Definition itoSum (A : I -> Prop) (i : I) (x : IExt ISumS ISumP ISumR A i) : (F ::+:: G) A i.
      destruct x; destruct s as [s|s].
      constructor 1.
      apply ito.
      constructor 1 with (s := s).
      apply pf.
      constructor 2.
      apply ito.
      constructor 1 with (s := s).
      apply pf.
    Defined.

    Global Instance IContainerSum : IContainer (F ::+:: G) :=
    {| IS      := ISumS;
       IP      := ISumP;
       IR      := ISumR;
       ito     := itoSum;
       ifrom   := ifromSum |}.
    Proof.
      (* ito_from *)
      intros.
      destruct a as [x|x]; simpl;
      remember (ifrom x) as e;
      destruct e; simpl;
      rewrite Heqe;
      rewrite ito_ifrom_inverse;
      reflexivity.
      (* from_to *)
      intros.
      destruct a.
      destruct s; simpl;
      rewrite ifrom_ito_inverse;
      reflexivity.
    Defined.

  End Sums.

End IndexedClass.

Hint Extern 0 (@FPAlgebra _ _ (_ :+: _) _ _) =>
  apply FPAlgebra_Plus_cont : typeclass_instances.

Hint Extern 0 (@FPAlgebra _ _ (_ :+: _) _ _) =>
  apply FPAlgebra_Plus_cont_inject2 : typeclass_instances.
