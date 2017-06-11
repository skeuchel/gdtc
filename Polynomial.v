Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.

Require Import Containers.
Require Import Functors.
Require Import List.
Require Import FunctionalExtensionality.

Inductive Code : Set :=
| U : Code
| I : Code
| C : Code -> Code -> Code
| P : Code -> Code -> Code.

Inductive ExtP (A : Set) : Code -> Set :=
| eu : ExtP A U
| ei : A -> ExtP A I
| el : forall {c1} {c2}, ExtP A c1 -> ExtP A (C c1 c2)
| er : forall {c1} {c2}, ExtP A c2 -> ExtP A (C c1 c2)
| ep : forall {c1} {c2}, ExtP A c1 -> ExtP A c2 -> ExtP A (P c1 c2).

Inductive FixP (c : Code) : Set := fixp : ExtP (FixP c) c -> FixP c.

Fixpoint pmap {A : Set} {B : Set} (f : A -> B) {c} (x : ExtP A c) : ExtP B c :=
  match x in ExtP _ c return ExtP B c with
    | eu         => eu _
    | ei x       => ei _ (f x)
    | el _ _ x   => el _ (pmap f x)
    | er _ _ y   => er _ (pmap f y)
    | ep _ _ x y => ep _ (pmap f x) (pmap f y)
  end.

Lemma pmap_fusion {A B D : Set} (f : A -> B) (g : B -> D) {c} (a : ExtP A c) :
  pmap g (pmap f a) = pmap (fun e => g (f e)) a.
Proof.
  induction a; simpl; auto; f_equal; auto.
Qed.

Lemma pmap_reflection {A : Set} {c} (a : ExtP A c) :
  pmap (fun x => x) a = a.
Proof.
  induction a; simpl; auto; f_equal; auto.
Qed.

Section Induction.
  Variable c : Code.
  Variable P0 : FixP c -> Prop.
  Variable P1 : forall d, ExtP (FixP c) d -> Prop.
  Variable ff : forall x, P1 c x -> P0 (fixp c x).
  Variable fu : P1 U (eu _).
  Variable fi : forall x, P0 x -> P1 I (ei _ x).
  Variable fl : forall c1 c2 x, P1 c1 x -> P1 (C c1 c2) (el _ x).
  Variable fr : forall c1 c2 y, P1 c2 y -> P1 (C c1 c2) (er _ y).
  Variable fp : forall c1 c2 x y, P1 c1 x -> P1 c2 y -> P1 _ (ep _ x y).

  Fixpoint fixp_ind (x : FixP c) : P0 x :=
    let fix extp_ind (d : Code) (x : ExtP _ d) : P1 _ x :=
        match x in ExtP _ d return P1 _ x with
          | eu => fu
          | ei x => fi x (fixp_ind x)
          | el c1 c2 x => fl c1 c2 x (extp_ind _ x)
          | er c1 c2 y => fr c1 c2 y (extp_ind _ y)
          | ep c1 c2 x y => fp c1 c2 x y (extp_ind _ x) (extp_ind _ y)
        end
    in
      match x return P0 x with
        | fixp x => ff x (extp_ind _ x)
      end.

End Induction.

Section Fold.
  Context {c : Code}.
  Context {A : Set}.
  Variable f : ExtP A c -> A.

  Fixpoint fixpfold (x : FixP c) : A :=
    let fix extfold (d : Code) (x : ExtP (FixP c) d) : ExtP A d :=
        match x in ExtP _ d return ExtP A d with
          | eu => eu _
          | ei x => ei _ (fixpfold x)
          | el _ _ x => el _ (extfold _ x)
          | er _ _ y => er _ (extfold _ y)
          | ep _ _ x y => ep _ (extfold _ x) (extfold _ y)
        end
    in match x with
         | fixp x => f (extfold _ x)
       end.

  Fixpoint extfold (d : Code) (x : ExtP (FixP c) d) : ExtP A d :=
    match x in ExtP _ d return ExtP A d with
      | eu => eu _
      | ei x => ei _ (fixpfold x)
      | el _ _ x => el _ (extfold _ x)
      | er _ _ y => er _ (extfold _ y)
      | ep _ _ x y => ep _ (extfold _ x) (extfold _ y)
    end.

  Lemma extfold_computation (d : Code) (g : ExtP A d -> A) :
    forall a, g (extfold _ a) = g (pmap fixpfold a).
  Proof.
    induction a; simpl; try reflexivity.
    apply (IHa (fun x => g (el A x))).
    apply (IHa (fun x => g (er A x))).
    rewrite (IHa1 (fun x => g (ep A x (extfold _ a2)))).
    rewrite (IHa2 (fun x => g (ep A (pmap fixpfold a1) x))).
    reflexivity.
  Qed.

  Lemma fixfold_computation :
    forall a, fixpfold (fixp _ a) = f (pmap fixpfold a).
  Proof.
    apply extfold_computation.
  Qed.

  Variable h : FixP c -> A.
  Variable H : forall (e : ExtP (FixP c) c), h (fixp _ e) = f (pmap h e).

  Fixpoint fixfold_uniqueness y : h y = fixpfold y.
    assert (forall (d : Code) (g : ExtP A d -> A)
                   (x : ExtP (FixP c) d), g (pmap h x) = g (extfold _ x))
           as extfold_uniqueness.
    induction x; simpl; auto.
    rewrite fixfold_uniqueness; reflexivity.
    rewrite (IHx (fun x => g (el A x))); reflexivity.
    rewrite (IHx (fun x => g (er A x))); reflexivity.
    rewrite (IHx1 (fun x => g (ep A x (pmap h x2)))).
    rewrite (IHx2 (fun x => g (ep A (extfold _ x1) x))).
    reflexivity.
    destruct y.
    rewrite H.
    apply extfold_uniqueness.
  Qed.
End Fold.

Lemma fixfold_reflection (c : Code) (x : FixP c) :
  fixpfold (fixp _) x = x.
Proof.
  apply sym_eq.
  apply (fixfold_uniqueness (fixp _) id).
  intro.
  unfold id at 1.
  apply sym_eq.
  f_equal.
  apply pmap_reflection.
Qed.

Class Polynomial (F : Set -> Set) :=
  { PCode             : Code;
    pto               : forall {A : Set}, ExtP A PCode -> F A;
    pfrom             : forall {A : Set}, F A -> ExtP A PCode;
    pto_pfrom_inverse : forall {A : Set} (a : F A), pto (pfrom a) = a;
    pfrom_pto_inverse : forall {A : Set} (a : ExtP A PCode), pfrom (pto a) = a
  }.

Section Sums.

  Variable F : Set -> Set.
  Context {poly_F : Polynomial F}.

  Variable G : Set -> Set.
  Context {poly_G : Polynomial G}.

  Definition ptoSum (A : Set) (x : ExtP A (C (@PCode F _) (@PCode G _))) : (F :+: G) A.
    inversion x; subst.
    left; apply pto; auto.
    right; apply pto; auto.
  Defined.

  Definition pfromSum (A : Set) (x : (F :+: G) A) : ExtP A (C (@PCode F _) (@PCode G _)).
    destruct x.
    apply (el _ (pfrom f)).
    apply (er _ (pfrom g)).
  Defined.

  Global Instance PolynomialSum : Polynomial (F :+: G) | 6 :=
  {| PCode    := C (@PCode F _) (@PCode G _);
     pto      := ptoSum;
     pfrom    := pfromSum |}.
  Proof.
    (* to_from *)
    intros;
    destruct a as [x|x];
    simpl;
    f_equal;
    apply pto_pfrom_inverse.
    (* from_to *)
    intros;
    dependent destruction a;
    simpl;
    f_equal;
    apply pfrom_pto_inverse.
  Defined.

End Sums.

Section Fold2.

  Variable c : Code.
  Variable A : Set.
  Variable B : Code -> Set.
  Variable ff : B c -> A.
  Variable fu : B U.
  Variable fi : A -> B I.
  Variable fl : forall c1 c2 : Code, B c1 -> B (C c1 c2).
  Variable fr : forall c1 c2 : Code, B c2 -> B (C c1 c2).
  Variable fp : forall c1 c2 : Code, B c1 -> B c2 -> B (P c1 c2).

  Fixpoint fixpfold2 (x : FixP c) : A :=
    let fix extpfold2 (d : Code) (y : ExtP (FixP c) d) : B d :=
        match y in ExtP _ d return B d with
          | eu           => fu
          | ei x         => fi (fixpfold2 x)
          | el c1 c2 x   => fl c1 c2 (extpfold2 c1 x)
          | er c1 c2 y   => fr c1 c2 (extpfold2 c2 y)
          | ep c1 c2 x y => fp c1 c2 (extpfold2 c1 x) (extpfold2 c2 y)
        end
    in
      match x with
        | fixp x => ff (extpfold2 c x)
      end.

  Definition extpfold2 :=
    fix extpfold2 (d : Code) (y : ExtP (FixP c) d) : B d :=
    match y in ExtP _ d return B d with
      | eu           => fu
      | ei x         => fi (fixpfold2 x)
      | el c1 c2 x   => fl c1 c2 (extpfold2 c1 x)
      | er c1 c2 y   => fr c1 c2 (extpfold2 c2 y)
      | ep c1 c2 x y => fp c1 c2 (extpfold2 c1 x) (extpfold2 c2 y)
    end.

  (*
  Fixpoint alg (d : Code) (x : ExtP A d) : B d :=
    match x in ExtP _ d return B d with
      | eu           => fu
      | ei x         => fi x
      | el c1 c2 x   => fl c1 c2 (alg c1 x)
      | er c1 c2 y   => fr c1 c2 (alg c2 y)
      | ep c1 c2 x y => fp c1 c2 (alg c1 x) (alg c2 y)
    end.

  Definition algebra (x : ExtP A c) : A := ff (alg c x).
  *)

End Fold2.

Section Equality.

  Class Eq (A : Set) :=
    { eq                     :  A -> A -> bool;
      eq_propositional_true  : forall (x y : A), eq x y = true  -> x = y;
      eq_propositional_false : forall (x y : A), eq x y = false -> x <> y
    }.

  Variable c : Code.

  Definition EQA := FixP c -> bool.
  Definition EQB (d : Code) := ExtP (FixP c) d -> bool.

  (*
  Fixpoint eqalg (d : Code) (x : ExtP EQA d) : EQB d.
  Proof.
    destruct x; intro y.
    apply true.
    inversion y.
    apply (e H).
    inversion y; subst.
    apply (eqalg _ _ H0).
    unfold
  *)

  Definition eqf (eq : EQB c) : EQA :=
    fun x => match x with
               | fixp e => eq e
             end.
  Definition equ (x : ExtP (FixP c) U) : bool := true.
  Definition eqi (f : EQA) : EQB I :=
    fun x => match x with
               | ei x => f x
               | _     => false
             end.
  Definition eql (c1 c2 : Code) (eq : EQB c1) : EQB (C c1 c2).
    intro x; inversion x; subst.
    apply (eq H0).
    apply false.
  Defined.
  Definition eqr (c1 c2 : Code) (eq : EQB c2) : EQB (C c1 c2).
    intro x; inversion x; subst.
    apply false.
    apply (eq H0).
  Defined.
  Definition eqp (c1 c2 : Code) (eq1 : EQB c1) (eq2 : EQB c2) : EQB (P c1 c2).
    intro x; inversion x; subst.
    apply (andb (eq1 H1) (eq2 H2)).
  Defined.

  Definition eqfix : FixP c -> FixP c -> bool :=
    fixpfold2 c EQA EQB eqf equ eqi eql eqr eqp.
  Definition eqext : forall d, ExtP (FixP c) d -> ExtP (FixP c) d -> bool :=
    extpfold2 c EQA EQB eqf equ eqi eql eqr eqp.

  Lemma eqfix_propositional_true :
    forall u v, eqfix u v = true -> u = v.
  Proof.
    apply (fixp_ind c
            (fun u   => forall v, eqfix u v = true -> u = v)
            (fun d u => forall v, eqext d u v = true -> u = v));
      intros;
      dependent destruction v;
      try (f_equal; apply (H _ H0));
      try discriminate.
    (* ep *)
    unfold eqext in H1.
    unfold extpfold2 in H1.
    simpl in H1.
    apply andb_true_iff in H1.
    destruct H1.
    f_equal.
    apply (H _ H1).
    apply (H0 _ H2).
  Qed.

  Lemma eqfix_propositional_false :
    forall u v, eqfix u v = false -> u <> v.
  Proof.
    apply (fixp_ind c
            (fun u   => forall v, eqfix u v = false -> u <> v)
            (fun d u => forall v, eqext d u v = false -> u <> v));
      intros;
      dependent destruction v;
      try discriminate;
      intro Heq; inversion Heq; subst.
    apply (H e); auto.
    apply (H f); auto.
    apply inj_pairT2 in H2.
    apply (H _ H0); auto.
    apply inj_pairT2 in H2.
    apply (H _ H0); auto.
    apply inj_pairT2 in H3.
    apply inj_pairT2 in H4.
    subst.
    unfold eqext in H1.
    unfold extpfold2 in H1.
    simpl in H1.
    apply andb_false_iff in H1.
    destruct H1.
    apply (H _ H1); auto.
    apply (H0 _ H1) ; auto.
  Qed.

  Global Instance Eq_FixP : Eq (FixP c) :=
    {| eq := eqfix;
       eq_propositional_true := eqfix_propositional_true;
       eq_propositional_false := eqfix_propositional_false |}.

End Equality.

Section Container.

  Fixpoint PShape (c : Code) : Set :=
    match c with
     | U     => unit
     | I     => unit
     | C c d => PShape c + PShape d
     | P c d => PShape c * PShape d
    end%type.

  Fixpoint PPos (c : Code) : PShape c -> Set :=
    match c return PShape c -> Set with
     | U     => fun s => Empty_set
     | I     => fun s => unit
     | C c d => fun s => match s with
                           | inl s1 => PPos c s1
                           | inr s2 => PPos d s2
                         end
     | P c d => fun s => match s with
                           | (s1 , s2) => PPos c s1 + PPos d s2
                         end
    end%type.

  Fixpoint fromPolynomial (A : Set) (c : Code) (x : ExtP A c) : Ext (PShape c) (PPos c) A.
  Proof.
    destruct x; simpl.
    constructor.
    constructor.
    intros.
    destruct H.
    constructor.
    constructor.
    intros.
    apply a.
    destruct (fromPolynomial A c1 x).
    constructor 1 with (s := inl _ s).
    apply pf.
    destruct (fromPolynomial A c2 x).
    constructor 1 with (s := inr _ s).
    apply pf.
    destruct (fromPolynomial A c1 x1) as [s1 pf1].
    destruct (fromPolynomial A c2 x2) as [s2 pf2].
    constructor 1 with (s := (s1 , s2)).
    intro p.
    destruct p.
    apply (pf1 p).
    apply (pf2 p).
  Defined.

  Lemma fromPolynomial_natural (c : Code) (A B : Set) (f : A -> B) :
    forall (x : ExtP A c),
      gmap _ _ f (fromPolynomial _ _ x) = fromPolynomial _ _ (pmap f x).
  Proof.
    induction x; simpl.
    f_equal; extensionality x; destruct x.
    reflexivity.
    destruct (fromPolynomial A c1 x).
    inversion IHx.
    reflexivity.
    destruct (fromPolynomial A c2 x).
    inversion IHx.
    reflexivity.
    destruct (fromPolynomial A c1 x1).
    destruct (fromPolynomial A c2 x2).
    inversion IHx1.
    inversion IHx2.
    simpl in *.
    f_equal.
    extensionality x; destruct x; reflexivity.
  Qed.

  Fixpoint toPolynomial' (A : Set) (c : Code) : forall (s : PShape c) (pf : PPos c s -> A), ExtP A c.
    destruct c; simpl; intros s pf.
    constructor.
    constructor. auto.
    destruct s as [s|s].
    apply el.
    apply (toPolynomial' A c1 s pf).
    apply er.
    apply (toPolynomial' A c2 s pf).
    destruct s as [s1 s2].
    constructor.
    apply (toPolynomial' A c1 s1).
    intro p.
    apply pf.
    left.
    apply p.
    apply (toPolynomial' A c2 s2).
    intro p.
    apply pf.
    right.
    apply p.
  Defined.

  Definition toPolynomial (A : Set) (c : Code) (x : Ext (PShape c) (PPos c) A) :=
    match x with
      | ext s pf => toPolynomial' A c s pf
    end.

  Lemma toPolynomial_natural (c : Code) (A B : Set) (f : A -> B) :
    forall (x : Ext (PShape c) (PPos c) A),
      pmap f (toPolynomial _ _ x) = toPolynomial _ _ (gmap _ _ f x).
  Proof.
    destruct x; simpl.
    induction c; try reflexivity.
    destruct s; simpl.
    rewrite IHc1; reflexivity.
    rewrite IHc2; reflexivity.
    destruct s; simpl.
    rewrite IHc1.
    rewrite IHc2.
    reflexivity.
  Qed.

  Lemma toPolynomial_fromPolynomial_inverse (A : Set) (c : Code) :
    forall (x : ExtP A c),
      toPolynomial A c (fromPolynomial A c x) = x.
  Proof.
    unfold toPolynomial in *.
    induction c; simpl.
    intros x.
    dependent destruction x.
    reflexivity.
    intros x.
    dependent destruction x.
    reflexivity.
    intros x.
    dependent destruction x; simpl.
    remember (fromPolynomial A c1 x).
    destruct e; simpl.
    rewrite <- (IHc1 x).
    rewrite <- Heqe.
    reflexivity.
    remember (fromPolynomial A c2 x).
    destruct e; simpl.
    rewrite <- (IHc2 x).
    rewrite <- Heqe.
    reflexivity.
    intros x.
    dependent destruction x; simpl.
    remember (fromPolynomial A c1 x1) as e1.
    remember (fromPolynomial A c2 x2) as e2.
    destruct e1; destruct e2; simpl.
    rewrite <- (IHc1 x1).
    rewrite <- (IHc2 x2).
    rewrite <- Heqe1.
    rewrite <- Heqe2.
    repeat rewrite <- eta_expansion.
    reflexivity.
  Qed.

  Lemma fromPolynomial_toPolynomial_inverse (A : Set) (c : Code) :
    forall (x : Ext (PShape c) (PPos c) A),
      fromPolynomial A c (toPolynomial A c x) = x.
  Proof.
    unfold toPolynomial in *.
    induction c; destruct x; simpl.
    destruct s; f_equal; extensionality x; destruct x; auto.
    destruct s; f_equal; extensionality x; destruct x; auto.
    destruct s as [s|s]; simpl.
    rewrite (IHc1 (ext _ _ s pf)); reflexivity.
    rewrite (IHc2 (ext _ _ s pf)); reflexivity.
    destruct s as [s1 s2]; simpl.
    remember (fun p : PPos c1 s1 => pf (inl (PPos c2 s2) p)) as pf1.
    remember (fun p : PPos c2 s2 => pf (inr (PPos c1 s1) p)) as pf2.
    rewrite (IHc1 (ext _ _ s1 pf1)).
    rewrite (IHc2 (ext _ _ s2 pf2)).
    f_equal; extensionality x; destruct x; subst; auto.
  Qed.

  Definition fromFixP (c : Code) : FixP c -> W _ (PPos c) :=
    fixpfold (fun x => sup _ _ (fromPolynomial _ _ x)).

  Definition toFixP (c : Code) : W _ (PPos c) -> FixP c :=
    gfold _ _ (fun x => fixp _ (toPolynomial _ _ x)).

  Lemma fromFixP_toFixP_inverse (c : Code) :
    forall (x : W _ _), fromFixP c (toFixP c x) = x.
  Proof.
    intro x.
    rewrite (gfold_uniqueness _ _ (sup _ _) (fun x => fromFixP c (toFixP c x))).
    apply gfold_reflection.
    intros.
    unfold toFixP.
    rewrite gfold_computation.
    unfold fromFixP.
    rewrite fixfold_computation.
    rewrite toPolynomial_natural.
    rewrite fromPolynomial_toPolynomial_inverse.
    rewrite gmap_fusion.
    reflexivity.
  Qed.

  Lemma toFixP_fromFixP_inverse (c : Code) :
    forall (x : FixP c), toFixP c (fromFixP c x) = x.
  Proof.
    intro x.
    rewrite (fixfold_uniqueness (fixp c) (fun x => toFixP c (fromFixP c x))).
    apply fixfold_reflection.
    intros.
    unfold fromFixP.
    rewrite fixfold_computation.
    unfold toFixP.
    rewrite gfold_computation.
    rewrite fromPolynomial_natural.
    rewrite toPolynomial_fromPolynomial_inverse.
    rewrite pmap_fusion.
    reflexivity.
  Qed.

  Instance PolynomialContainer (F : Set -> Set) {poly_F : Polynomial F} :
    Container F :=
  {| Shape    := PShape PCode;
     Position := PPos PCode;
     from     := fun A x => fromPolynomial A PCode (pfrom x);
     to       := fun A x => pto (toPolynomial A PCode x) |}.
  Proof.
    intros.
    rewrite toPolynomial_fromPolynomial_inverse.
    apply pto_pfrom_inverse.
    intros.
    rewrite pfrom_pto_inverse.
    apply fromPolynomial_toPolynomial_inverse.
  Defined.

  Global Instance Eq_Fix (F : Set -> Set) {poly_F : Polynomial F} :
    Eq (Fix F) := {| eq := fun x y => eq (toFixP _ x) (toFixP _ y) |}.
  Proof.
    intros; simpl.
    apply eq_propositional_true in H.
    apply f_equal with (f := fromFixP PCode) in H.
    repeat rewrite fromFixP_toFixP_inverse in H.
    auto.
    intros.
    apply eq_propositional_false in H.
    intro.
    apply H.
    f_equal.
    auto.
  Defined.

  Global Instance WF_Functor_plus_poly_inl
    {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Poly_G : Polynomial G}
    {Poly_H : Polynomial H}
    {subfg : F :<: G}
    {WF_Fun_F : WF_Functor F _ subfg}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inl F G H _ ) (Fun_G := ContainerFunctor (G :+: H)) | 1.
  Proof.
    constructor; simpl; intros.
    rewrite <- wf_functor; simpl.
    destruct (fromPolynomial A PCode (pfrom (inj fa))).
    reflexivity.
  Defined.

  Global Instance WF_Functor_plus_poly_inr
    {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Poly_G : Polynomial G}
    {Poly_H : Polynomial H}
    {subfh : F :<: H}
    {WF_Fun_F : WF_Functor F _ subfh}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inr F G H _ ) (Fun_G := ContainerFunctor (G :+: H)) | 1.
  Proof.
    constructor; simpl; intros.
    rewrite <- wf_functor; simpl.
    destruct (fromPolynomial A PCode (pfrom (inj fa))).
    reflexivity.
  Defined.

  Global Instance WF_Functor_plus_poly_inl'
    {F G H : Set -> Set}
    {Cont_F : Polynomial F}
    {Cont_G : Polynomial G}
    {Fun_H : Functor H}
    {sub_FG_H : (F :+: G) :<: H}
    {WF_Fun_FG_H : WF_Functor _ _ sub_FG_H (Fun_F := ContainerFunctor (F :+: G))}
    :
    WF_Functor _ _ (Sub_Functor_inl' sub_FG_H).
  Proof.
    constructor; intros; simpl.
    rewrite wf_functor; simpl.
    destruct (fromPolynomial A PCode (pfrom fa)).
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
    WF_Functor _ _ (Sub_Functor_inr' sub_FG_H).
  Proof.
    constructor; intros; simpl.
    rewrite wf_functor; simpl.
    destruct (from fa).
    reflexivity.
  Defined.

End Container.

Infix "*" := (P) : polynomial_scope.
Infix "+" := (C) : polynomial_scope.
Notation "1" := U : polynomial_scope.
Arguments ExtP A%type_scope C%polynomial_scope.
Delimit Scope polynomial_scope with poly.
