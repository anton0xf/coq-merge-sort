Print False.
Print True.
Print bool.


Inductive Bott : Prop :=.
Inductive Unit : Prop := I.
Inductive Bool : Set := t | f.
Definition neg (b: Bool) :=
  match b with
  | t => f
  | f => t
  end.
Theorem double_neg (b: Bool) : neg (neg b) = b.
Proof.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition double_neg' (b: Bool) : neg (neg b) = b :=
  match b with
  | t => eq_refl
  | f => eq_refl
  end.

Inductive NatList : Type :=
 | Nil
 | Cons (x: nat) (xs: NatList).

Check Nil.
Check (Cons 3 Nil).

Fixpoint len (xs: NatList) :=
  match xs with
  | Nil => 0
  | Cons x xs' => 1 + len xs'
  end.

Theorem cons_len (x: nat) (xs: NatList): len (Cons x xs) = 1 + len xs.
Proof.
  destruct xs as [| x1 xs1]; auto.
  (* - simpl. reflexivity. *)
  (* - simpl. reflexivity. *)
Qed.

Definition g := (fun x y: Prop => x -> y).
Check g True.



