Require Import List.

Ltac caseEq x := generalize (refl_equal x); pattern x at -1; case x; intros.

Definition marked(P:Prop) : Prop := P.

Ltac mark H :=
  let t := type of H in
  let n:= fresh in
    (assert (n:marked t); [exact H | clear H; rename n into H]).

Ltac unmark H := unfold marked in H.

Ltac unmark_all := unfold marked in *|-.

Ltac revert_all H :=
  mark H;
  match goal with 
    | H0 : _, H : marked _ |- _ => revert H0; revert_all H
    | _ => idtac
  end;
  unmark_all.

Ltac Prop_Ind1 H A := 
  let HA' := fresh A "'" in 
    assert (exists A', A = A') as HA' by eauto; destruct HA';
      revert_all H; 
      induction H.

Ltac Prop_Ind2 H A B:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
    let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
      revert_all H;
      induction H. 

Ltac Prop_Ind3 H A B C:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
    revert_all H;
    induction H.

Ltac Prop_Ind4 H A B C D:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
  let HD' := fresh D "'" in assert (exists D', D = D') as HD' by eauto; destruct HD';
    revert_all H; 
    induction H.

Ltac Prop_Ind5 H A B C D E:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
  let HD' := fresh D "'" in assert (exists D', D = D') as HD' by eauto; destruct HD';
  let HE' := fresh E "'" in assert (exists E', E = E') as HE' by eauto; destruct HE';
    revert_all H;
    induction H.

Ltac Prop_Ind H :=
  match (type of H) with 
    | ?P ?A ?B ?C ?D ?E => Prop_Ind5 H A B C D E
    | ?P ?A ?B ?C ?D=> Prop_Ind4 H A B C D 
    | ?P ?A ?B ?C => Prop_Ind3 H A B C 
    | ?P ?A ?B=> Prop_Ind2 H A B
    | ?P ?A => Prop_Ind1 H A
    | _ => idtac
  end.

Ltac Prop_Ind_test H :=
  match (type of H) with 
    | ?P ?A ?B ?C ?D ?E => idtac "PI5"; Prop_Ind5 H A B C D E
    | ?P ?A ?B ?C ?D=> idtac "PI4"; Prop_Ind4 H A B C D 
    | ?P ?A ?B ?C => idtac "PI3"; Prop_Ind3 H A B C 
    | ?P ?A ?B=> idtac "PI2"; Prop_Ind2 H A B
    | ?P ?A => idtac "PI1"; Prop_Ind1 H A
    | _ => idtac
  end.

Ltac Prop_Destruct1 H A := 
  let HA' := fresh A "'" in 
    assert (exists A', A = A') as HA' by eauto; destruct HA';
      revert_all H; 
      destruct H.

Ltac Prop_Destruct2 H A B:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
    let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
      revert_all H;
      destruct H. 

Ltac Prop_Destruct3 H A B C:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
    revert_all H;
    destruct H.

Ltac Prop_Destruct4 H A B C D:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
  let HD' := fresh D "'" in assert (exists D', D = D') as HD' by eauto; destruct HD';
    revert_all H; 
    destruct H.

Ltac Prop_Destruct5 H A B C D E:= 
  let HA' := fresh A "'" in assert (exists A', A = A') as HA' by eauto; destruct HA';
  let HB' := fresh B "'" in assert (exists B', B = B') as HB' by eauto; destruct HB';
  let HC' := fresh C "'" in assert (exists C', C = C') as HC' by eauto; destruct HC';
  let HD' := fresh D "'" in assert (exists D', D = D') as HD' by eauto; destruct HD';
  let HE' := fresh E "'" in assert (exists E', E = E') as HE' by eauto; destruct HE';
    revert_all H;
    destruct H.

Ltac Prop_Destruct H :=
  match (type of H) with 
    | ?P ?A ?B ?C ?D ?E => Prop_Ind5 H A B C D E
    | ?P ?A ?B ?C ?D=> Prop_Ind4 H A B C D 
    | ?P ?A ?B ?C => Prop_Ind3 H A B C 
    | ?P ?A ?B=> Prop_Ind2 H A B
    | ?P ?A => Prop_Ind1 H A
    | _ => idtac
  end.

Inductive List_P1 {A : Type} (P : A -> Prop) : list A -> Prop :=
  Cons_a : forall c cs', P c -> List_P1 P cs' -> List_P1 P (c :: cs')
| Nil : List_P1 P nil.

Lemma In_List_P1 : forall A (P : A -> Prop) (As : list A), 
  (forall a, In a As -> P a) -> List_P1 P As.
  induction As; intros.
  constructor.
  simpl; constructor.
  apply H; simpl; auto.
  apply IHAs; intros; apply H; simpl; auto.
Qed.

Lemma In_List_P1' : forall A (P : A -> Prop) (As : list A), 
  List_P1 P As -> (forall a, In a As -> P a).
  induction As; simpl; intros; inversion H; destruct H0; subst; eauto.
Qed.

(*** Definition List_P1 {A : Type} (as' : list A) (P : A -> Prop) : Prop :=
  forall a n, nth_error as' n = Some a -> P a. ***)

Definition List_P2 {A B : Type} (as' : list A) (bs : list B) (P : A -> B -> Prop) : Prop :=
  (forall a n, nth_error as' n = Some a -> exists b, nth_error bs n = Some b /\ P a b) /\
  (forall n, nth_error as' n = None -> nth_error bs n = None).

Lemma nth_error_nil : forall n A, nth_error nil n = @None A.
  intros; destruct n; simpl; reflexivity.
Qed.

Lemma nth_error_in : forall B (Bs : list B) b n, nth_error Bs n = Some b -> In b Bs.
  induction Bs; intros; destruct n; simpl in *|-*; try discriminate.
  injection H; tauto.
  right; eauto.
Qed.

Lemma nth_error_in' : forall B (Bs : list B) b, In b Bs -> exists n, nth_error Bs n = Some b.
  induction Bs; intros; simpl in *|-*.
  tauto.
  destruct H.
  exists 0; simpl; subst; reflexivity.
  destruct (IHBs _ H) as [n nth_n]; exists (S n); assumption.
Qed.

Lemma List_P2_cons : forall (A B : Type) a as' b bs' (P : A -> B -> Prop),
  List_P2 (a :: as') (b :: bs') P -> P a b /\ List_P2 as' bs' P.
  unfold List_P2; intros until P; intro P2_Cons; destruct P2_Cons as [fnd not_fnd].
  repeat split; intros.
  destruct (fnd _ 0 (refl_equal _)) as [b0 [b0_eq Pab']]; simpl in b0_eq; 
    injection b0_eq; intros; subst; assumption.
  eapply (fnd _ (S n) H).
  eapply (not_fnd (S n)); simpl; eauto.
Qed.

Lemma cons_List_P2 : forall (A B : Type) a as' b bs' (P : A -> B -> Prop),
  P a b -> List_P2 as' bs' P -> List_P2 (a :: as') (b :: bs') P.
  unfold List_P2; intros; destruct H0; split; destruct n; simpl; intros.
  injection H2; intros; subst; exists b; split; auto.
  eauto.
  discriminate.
  eauto.
Qed.

Ltac P1_nil H := rewrite nth_error_nil in H; discriminate.

Lemma List_P2_nil : forall (A B : Type) a as' (P : A -> B -> Prop),
  ~ List_P2 (a :: as') nil P.
  unfold List_P2; unfold not; intros until P; intros P2; destruct P2 as [fnd _].
  destruct (fnd _ 0 (refl_equal _)) as [b [Error _]]; discriminate Error.
Qed.    

Lemma List_P2_nil' : forall (A B : Type) b bs' (P : A -> B -> Prop),
  ~ List_P2 nil (b :: bs') P.
  unfold List_P2; unfold not; intros until P; intros P2; destruct P2 as [_ not_fnd].
  generalize (not_fnd 0 (refl_equal _)) as Error; intros; discriminate Error.
Qed.

Ltac P2_nil H := try (elimtype False; eapply (List_P2_nil _ _ _ _ _ H); fail); try
  (elimtype False; eapply (List_P2_nil' _ _ _ _ _ H); fail).


Inductive List_P2' {A B : Type} (P : A -> B -> Prop) : list A -> list B -> Prop :=
| nil_P2' : List_P2' P nil nil
| cons_P2' : forall a b As Bs, P a b -> List_P2' P As Bs -> List_P2' P (a :: As) (b :: Bs).

Lemma P2_if_P2' : forall A B (as' : list A) (bs : list B) (P : A -> B -> Prop), 
  List_P2 as' bs P -> List_P2' P as' bs.
  induction as'; intros; destruct bs; try P2_nil H; econstructor.
  destruct H as [fnd _].
  destruct (fnd _ 0 (refl_equal _)) as [b0 [b0_eq P_b0]].
  simpl in b0_eq; inversion b0_eq; subst; assumption.
  eapply IHas'.
  destruct (List_P2_cons _ _ _ _ _ _ _ H); assumption.
Qed.
  
Lemma P2'_if_P2 : forall A B (as' : list A) (bs : list B) (P : A -> B -> Prop), 
  List_P2' P as' bs -> List_P2 as' bs P.
  intros; Prop_Ind H; intros.
  clear; unfold List_P2; split; intros.
  destruct n; simpl in H; discriminate.
  destruct n; simpl; reflexivity.
  eapply cons_List_P2; eauto.
Qed.
  
Lemma nil_List_P2 : forall (A B : Type) (P : A -> B -> Prop),
  List_P2 nil nil P.
  unfold List_P2; intros; split; intros; destruct n; simpl in *|-*; try discriminate; reflexivity.
Qed.

Fixpoint zip {A B C : Type} (As : list A) (Bs : list B) (f : A -> B -> C) : option (list C) := 
  match As, Bs with 
    a :: As', b :: Bs' => match zip As' Bs' f with
                            Some Cs => Some ((f a b) :: Cs)
                            | _ => None
                          end
    | nil, nil => Some nil
    | _, _ => None
  end.

Fixpoint opt_map {A B : Type} (As : list A) (f : A -> option B) : option (list B) := 
  match As with 
    a :: As' => match (opt_map As' f) with
                  | Some Bs => match f a with 
                                 Some b => Some (b :: Bs)
                                 | _ => None
                               end
                  | None => None
                end
    | nil => Some nil
  end.

Fixpoint distinct (A : Type) (l : list A) : Prop :=
  match l with 
    nil => True
    | cons a l' => (~ In a l') /\ distinct A l'
  end.

Lemma nth_error_map : forall A B (f : A -> B) As n a,
  nth_error As n = Some a -> nth_error (map f As) n = Some (f a).
  clear; induction As; destruct n; simpl; intros; try discriminate.
  injection H; intros; subst; reflexivity.
  eauto.
Qed.

Lemma nth_error_map' : forall A B (f : A -> B) As n,
  nth_error As n = None -> nth_error (map f As) n = None.
  clear; induction As; destruct n; simpl; intros; try discriminate; auto.
Qed.

Lemma map_nth_error : forall A B (f : A -> B) As n a,
  nth_error (map f As) n = Some a ->  exists a', nth_error As n = Some a' /\ a = f a'.
  clear; induction As; destruct n; simpl; intros; try discriminate.
  injection H; intros; subst. exists a; split; auto.
  eauto.
Qed.

Lemma map_nth_error' : forall A B (f : A -> B) As n,
  nth_error (map f As) n = None -> nth_error As n = None.
  clear; induction As; destruct n; simpl; intros; try discriminate; auto.
Qed.


Implicit Arguments distinct [A].

  Lemma distinct_sym : forall B (Bs Bs' : list B), distinct (Bs ++ Bs') -> distinct (Bs' ++ Bs).
    clear; induction Bs; simpl.
    intros; rewrite <- app_nil_end; assumption.
    intros Bs' H; destruct H; simpl.
    generalize a Bs (IHBs _  H0) H; clear; induction Bs'.
    simpl; intros; rewrite <- app_nil_end in H0; tauto.
    simpl; intros; destruct H; unfold not; split; intros.
    assert (a = a0).
    generalize Bs' a a0 Bs H H2; clear; induction Bs'; simpl; intros.
    destruct H2; auto; elimtype False; eauto.
    destruct H2.
    elimtype False; eauto.
    assert (~ In a0 (Bs' ++ Bs)) by (unfold not; intros; eauto); eauto.
    subst; eauto.
    apply H0; generalize Bs; clear; induction Bs; simpl; intros; eauto.
    eapply IHBs'; eauto.
    unfold not; intros H2; apply H0; generalize Bs' a a0 H2; clear; induction Bs; 
      simpl; intros; try tauto.
    destruct H2; try tauto.
    right; eapply IHBs; assumption.
  Qed.

Inductive id_map_1 {A B : Set} : A -> B -> B -> Prop :=
  idm1 : forall a b, id_map_1 a b b.

Inductive id_map_2 {A B C : Set} : A -> B -> C -> C -> Prop :=
  idm2 : forall a b c, id_map_2 a b c c.

Inductive id_map_3 {A B C D : Set} : A -> B -> C -> D -> D -> Prop :=
  idm3 : forall a b c d, id_map_3 a b c d d.

Inductive id_map_4 {A B C D E : Set} : A -> B -> C -> D -> E -> E -> Prop :=
  idm4 : forall a b c d e, id_map_4 a b c d e e.

Inductive id_map_5 {A B C D E F: Set} : A -> B -> C -> D -> E -> F -> F -> Prop :=
  idm5 : forall a b c d e f, id_map_5 a b c d e f f.

  Lemma length_List_P2' : forall A B (as' : list A) (bs : list B) (P : A -> B -> Prop), 
    List_P2' P as' bs -> length as' = length bs.
    induction as'; intros; destruct bs; inversion H; auto.
    simpl; eauto.
  Qed.

  Lemma length_List_P2 : forall A B (as' : list A) (bs : list B) (P : A -> B -> Prop), 
    List_P2 as' bs P -> length as' = length bs.
    intros; eapply length_List_P2'; apply P2_if_P2'; eassumption.
  Qed.

  Lemma List_P1_app : forall A (as' as'': list A) (P : A -> Prop), 
    List_P1 P as' -> List_P1 P as'' -> List_P1 P (as' ++ as'').
    clear; induction as'; intros; simpl; auto; inversion H; subst;
      constructor; auto.
  Qed.

  Lemma List_P2'_app : forall A B (as' as'': list A) (bs bs': list B) (P : A -> B -> Prop), 
    List_P2' P as' bs -> List_P2' P as'' bs' -> List_P2' P (as' ++ as'') (bs ++ bs').
    clear; induction as'; intros; inversion H; subst; simpl; auto;
      constructor; auto.
  Qed.

  Lemma List_P2_app : forall A B (as' as'': list A) (bs bs': list B) (P : A -> B -> Prop), 
    List_P2 as' bs P -> List_P2 as'' bs' P -> List_P2 (as' ++ as'') (bs ++ bs') P.
    clear; intros; apply P2_if_P2' in H; apply P2_if_P2' in H0; apply P2'_if_P2; apply List_P2'_app; auto.
  Qed.
