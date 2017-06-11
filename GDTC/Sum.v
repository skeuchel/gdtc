
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
