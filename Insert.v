Require Import Arith.
Require Import List.
Import ListNotations.

Fixpoint insert (x: nat) (xs: list nat) : list nat :=
  match xs with
  | nil => [x]
  | h :: t => if x <=? h then x :: xs else h :: insert x t
  end.

Compute insert 2 [1;3]. (* = [1; 2; 3] : list nat *)

Lemma insert_contains_x (x: nat) (xs: list nat): In x (insert x xs).
Proof.
  induction xs as [| h t IH].
  - (* xs = [] *) simpl. left. reflexivity.
  - (* xs = h :: t *) simpl. destruct (x <=? h).
    + (* x <= h *) simpl. auto.
    + (* x > h *) simpl. right. exact IH.
Qed.
