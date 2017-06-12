Require Import String.
Require Import Example.Base.
Require Import Example.Arith.
Require Import Example.Logic.
Require Import GDTC.Polynomial.
Require Import GDTC.Containers.
Require Import GDTC.Functors.

Open Scope string_scope.

Section Test_Section.

  Definition E := Arith :+: Logic.

  Definition ex_1 : Fix E :=
    (add E (lit _ 1) (lit _ 2)).
  Definition ex_2 : Fix E :=
    (add E (lit _ 5) (lit _ 0)).
  Definition ex_3 : Fix E :=
    (cond E (blit _ true) ex_1 ex_2).
  Definition ex_4 : Fix E :=
    (cond E (blit _ false) ex_1 ex_2).

  Eval compute in ("The depth of '1 + 2' should be 1.").
  Eval compute in (depthOf E ex_1).
  Eval compute in ("The depth of '145 + 2346' should be 1.").
  Eval compute in (depthOf E ex_2).
  Eval compute in ("The depth of 'true' should be 0.").
  Eval compute in (depthOf E (blit E true)).
  Eval compute in ("The depth of 'if true then (1 + 2) else (5 + 0)' should be 2.").
  Eval compute in (depthOf E ex_3).
  Eval compute in ("The depth of 'if false then (1 + 2) else (5 + 0)' should be 2.").
  Eval compute in (depthOf E ex_4).

  Eval compute in ("The size of '1 + 2' should be 3.").
  Eval compute in (sizeOf E ex_1).
  Eval compute in ("The size of '145 + 2346' should be 3.").
  Eval compute in (sizeOf E ex_2).
  Eval compute in ("The size of 'true' should be 1.").
  Eval compute in (sizeOf E (blit E true)).
  Eval compute in ("The size of 'if true then (1 + 2) else (5 + 0)' should be 8.").
  Eval compute in (sizeOf E ex_3).
  Eval compute in ("The size of 'if false then (1 + 2) else (5 + 0)' should be 8.").
  Eval compute in (sizeOf E ex_4).

  Lemma depthSizeAL : forall (e : Fix E), DepthSizeP E e.
  Proof. apply depthSize; eauto 200 with typeclass_instances. Qed.

  Eval compute in ("DepthSize for Arith :+: Bool Proven!").
  (* Eval compute in (depthSizeAL ex_1). *)
  (* Eval compute in (depthSizeAL ex_2). *)
  (* Eval compute in (depthSizeAL ex_3). *)
  (* Eval compute in (depthSizeAL ex_4). *)

End Test_Section.
