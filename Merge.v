Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Sorted.
From Coq Require Import Recdef.

(* https://coq.inria.fr/doc/v8.9/stdlib/Coq.Sorting.Permutation.html *)
Require Import Permutation.

(* === special induction === *)

(* provide explicit proof term
   https://softwarefoundations.cis.upenn.edu/vfa-current/Merge.html#lab96 *)
Definition list_ind2 {A: Type} (P: list A -> Prop)
  (H0: P []) (H1: (forall x: A, P [x]))
  (Hn: (forall (x1 x2: A) (xs: list A), P xs -> P (x1 :: x2 :: xs)))
  : (forall xs: list A, P xs) :=
  (fix IH (xs : list A) : P xs :=
     match xs with
     | [] => H0
     | [x] => H1 x
     | x1 :: x2 :: xs' => Hn x1 x2 xs' (IH xs')
     end).

(* same with [fix] tactic *)
Theorem list_ind2' {A: Type} (P: list A -> Prop):
  P [] ->
  (forall x: A, P [x]) ->
  (forall (x1 x2: A) (xs: list A), P xs -> P (x1 :: x2 :: xs)) ->
  (forall xs: list A, P xs).
Proof.
  intros H0 H1 Hn. fix IH 1. destruct xs as [|x1 xs1].
  - exact H0.
  - destruct xs1 as [|x2 xs2].
    + apply H1.
    + apply Hn, IH.
Qed.

(* using induction *)
Lemma list_ind2_aux {A: Type} (P: list A -> Prop):
  P [] ->
  (forall x: A, P [x]) ->
  (forall (x1 x2: A) (xs: list A), P xs -> P (x1 :: x2 :: xs)) ->
  (forall xs, P xs /\ forall x, P (x :: xs)).
Proof.
  intros H0 H1 Hn xs. induction xs as [|x1 xs1 [IHn IHn1]].
  - split; assumption.
  - split.
    + apply IHn1.
    + intro x2. apply Hn, IHn.
Qed.

Theorem list_ind2'' {A: Type} (P: list A -> Prop):
  P [] ->
  (forall x: A, P [x]) ->
  (forall (x1 x2: A) (xs: list A), P xs -> P (x1 :: x2 :: xs)) ->
  (forall xs: list A, P xs).
Proof.
  intros H0 H1 Hn xs. apply list_ind2_aux; assumption.
Qed.

(* === merge_sort implementation === *)
Fixpoint merge (xs ys: list nat): list nat :=
  let fix aux ys :=
    match xs, ys with
    | nil, _ => ys
    | _, nil => xs
    | x :: xs', y :: ys' => if x <=? y
                         then x :: merge xs' ys
                         else y :: aux ys'
    end
  in aux ys.

Example merge_nil_l: merge [] [1; 2] = [1; 2].
Proof. trivial. Qed.

Example merge_nil_r: merge [1] [] = [1].
Proof. trivial. Qed.

Example merge_ex: merge [1; 3; 4] [0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Fixpoint split_all (xs: list nat): list (list nat) :=
  match xs with
  | nil => nil
  | x :: xs' => [x] :: split_all xs'
  end.

Fixpoint merge_pairs (xss: list (list nat)): list (list nat) :=
  match xss with
  | [] => []
  | [xs] => [xs]
  | xs1 :: xs2 :: xs' => (merge xs1 xs2) :: merge_pairs xs'
  end.

Theorem merge_pairs_monotonic (xss: list (list nat)): length (merge_pairs xss) <= length xss.
Proof.
  apply (list_ind2 (fun yss: list (list nat) => length (merge_pairs yss) <= length yss));
    try trivial.
  intros x1 x2 xs IH. simpl. apply le_n_S, le_S, IH.
Qed.

Function merge_all (xss: list (list nat)) {measure length xss}: (list nat) :=
  match xss with
  | [] => []
  | [xs] => xs
  | _ => merge_all (merge_pairs xss)
  end.
Proof.
  intros xss xs1 _ xs2 xss' _ eq. simpl.
  apply le_n_S, le_n_S, merge_pairs_monotonic.
Defined.
  
(*
merge_all_tcc is declared
merge_all_terminate is defined
merge_all_rect is defined
merge_all_ind is defined
merge_all_rec is defined
R_merge_all_correct is defined
R_merge_all_complete is defined
*)

(* https://stackoverflow.com/a/52896140
   sort :: (Ord a) => [a] -> [a]
   sort = mergeAll . map (:[]) 
        where
            mergeAll [] = []
            mergeAll [t] = t
            mergeAll xs  = mergeAll (mergePairs xs)

            mergePairs (x:y:xs) = merge x y:mergePairs xs
            mergePairs xs = xs

https://coq.inria.fr/doc/v8.9/stdlib/Coq.Sorting.Mergesort.html
 *)
Definition merge_sort (xs: list nat): list nat := merge_all (split_all xs).

Compute merge_sort [2; 3; 1; 5; 4; 6; 4].
(* = Some [1; 2; 3; 4; 4; 5; 6] : option (list nat) *)

(* === Sorted === *)
Inductive Is_sorted: list nat -> Prop :=
| Nil_is_sorted: Is_sorted []
| Single_is_sorted (x: nat): Is_sorted [x]
| Cons2_is_sorted (x1 x2: nat) (xs: list nat):
  x1 <= x2 /\ Is_sorted (x2 :: xs) -> Is_sorted (x1 :: x2 :: xs).

Definition all_is_sorted (xss: list (list nat)): Prop := forall xs: list nat, In xs xss -> Is_sorted xs.

Theorem split_all_is_sorted (xs: list nat): all_is_sorted (split_all xs).
Proof.
  induction xs as [|x xs' IH].
  - simpl. intros ys H. destruct H.
  - simpl. intros ys [H | H].
    + subst ys. apply Single_is_sorted.
    + apply IH, H.
Qed.

Theorem rest_is_sorted (x: nat) (xs: list nat): Is_sorted (x :: xs) -> Is_sorted xs.
Proof.
  intro H. inversion H.
  - apply Nil_is_sorted.
  - apply H1.
Qed.

Inductive Le_all (x: nat): list nat -> Prop :=
| Le_all_nil: Le_all x []
| Le_all_cons (y: nat) (ys: list nat): x <= y -> Le_all x ys -> Le_all x (y :: ys).

Theorem le_all_head (x y: nat) (ys: list nat): Le_all x (y :: ys) -> x <= y.
Proof. intro H. inversion H. assumption. Qed.

Theorem le_all_rest (x y: nat) (ys: list nat): Le_all x (y :: ys) -> Le_all x ys.
Proof. intro H. inversion H. assumption. Qed.

Theorem le_all_trans (x y: nat) (ys: list nat): x <= y -> Le_all y ys -> Le_all x ys.
Proof.
  intros le_x_y le_y_ys. induction ys as [|y1 ys1 IH].
  - apply Le_all_nil.
  - apply Le_all_cons.
    + apply le_all_head in le_y_ys. apply (Nat.le_trans x y y1 le_x_y le_y_ys).
    + apply IH. apply (le_all_rest y y1 ys1 le_y_ys).
Qed.

Theorem le_all_trans_cons (x y: nat) (ys: list nat): x <= y -> Le_all y ys -> Le_all x (y :: ys).
Proof.
  intros le_x_y le_y_ys. apply Le_all_cons; try assumption.
  apply (le_all_trans x y ys); assumption.
Qed.

(* https://softwarefoundations.cis.upenn.edu/vfa-current/Merge.html#lab98 *)
Lemma merge2_le (x1 x2: nat) (xs1 xs2: list nat):
  x1 <= x2 -> merge (x1 :: xs1) (x2 :: xs2) = x1 :: merge xs1 (x2 :: xs2).
Proof.
  intro neq. simpl. apply leb_correct in neq. rewrite neq. reflexivity.
Qed.

Lemma merge2_gt (x1 x2: nat) (xs1 xs2: list nat):
  x1 > x2 -> merge (x1 :: xs1) (x2 :: xs2) = x2 :: merge (x1 :: xs1) xs2.
Proof.
  intro neq. simpl. apply leb_correct_conv in neq. rewrite neq. reflexivity.
Qed.

Theorem le_all_merge (x: nat) (xs ys: list nat):
  Le_all x xs -> Le_all x ys -> Le_all x (merge xs ys).
Proof.
  generalize dependent ys. induction xs as [|x1 xs1 IHxs].
  - (* xs = [] *) intros ys _ le_ys. simpl. destruct ys as [|y ys'].
    + apply Le_all_nil.
    + exact le_ys.
  - (*[ xs = x1 :: xs1 ]*) induction ys as [|y1 ys1 IHys].
    + (* ys = [] *) intros le_xs _. simpl. exact le_xs.
    + (*[ ys = y1 :: ys1 ]*) intros le_xs le_ys.
      apply le_all_head in le_xs as le_x1.
      apply le_all_rest in le_xs as le_xs1.
      apply le_all_head in le_ys as le_y1.
      apply le_all_rest in le_ys as le_ys1.
      destruct (x1 <=? y1) eqn:neq.
      * { (*[ x1 <= y1 ]*) apply leb_complete in neq as neq'.
          rewrite merge2_le; try assumption.
          apply Le_all_cons; try assumption.
          apply IHxs; assumption.
        }
      * { (*[ x1 > y1 ]*) apply leb_complete_conv in neq as neq'.
          rewrite merge2_gt; try assumption.
          apply Le_all_cons; try assumption.
          apply IHys; assumption.
        }
Qed.

Theorem cons_is_sorted (x: nat) (xs: list nat):
  Is_sorted xs -> Le_all x xs -> Is_sorted (x :: xs).
Proof.
  generalize dependent x.
  induction xs as [|y ys IH].
  - intros x _ _. apply Single_is_sorted.
  - intros x H le. apply Cons2_is_sorted. split.
    + apply (le_all_head x y ys). exact le.
    + exact H.
Qed.

Theorem head_of_sorted_le_next (x1 x2: nat) (xs: list nat): Is_sorted (x1 :: x2 :: xs) -> x1 <= x2.
Proof.
  intro H. inversion H. destruct H1 as [le _]. exact le.
Qed.

Theorem head_of_sorted_le_all (x: nat) (xs: list nat): Is_sorted (x :: xs) -> Le_all x xs.
Proof.
  generalize dependent x.
  apply (list_ind2 (fun ys: list nat => forall y : nat, Is_sorted (y :: ys) -> Le_all y ys)).
  - intros x _. apply Le_all_nil.
  - intros x2 x1 H. apply head_of_sorted_le_next in H.
    apply Le_all_cons. exact H. apply Le_all_nil.
  - intros x1 x2 xs2 IH y H.
    apply head_of_sorted_le_next in H as le_x1.
    apply rest_is_sorted in H as H1.
    apply Le_all_cons. exact le_x1.
    apply head_of_sorted_le_next in H1 as le_x2.
    apply rest_is_sorted in H1 as H2.
    apply le_all_trans_cons. apply (Nat.le_trans y x1 x2); assumption.
    apply IH. exact H2.
Qed.

Theorem merge_is_sorted (xs ys: list nat):
  Is_sorted xs -> Is_sorted ys -> Is_sorted (merge xs ys).
Proof.
  generalize dependent ys. induction xs as [|x xs' IHxs]; intro ys.
  - (* xs = [] *) simpl. destruct ys; auto.
  - (* xs = x :: xs' *) induction ys as [|y ys' IHys].
    + (* ys = [] *) trivial.
    + (* ys = y :: ys' *) intros xs_is_sorted ys_is_sorted.
      apply rest_is_sorted in xs_is_sorted as xs_is_sorted'.
      apply rest_is_sorted in ys_is_sorted as ys_is_sorted'.
      destruct (x <=? y) eqn:neq.
      * { (* x <= y *) apply leb_complete in neq as neq'.
          rewrite merge2_le; try assumption.
          apply cons_is_sorted.
          - apply IHxs; assumption.
          - apply le_all_merge.
            + apply head_of_sorted_le_all. exact xs_is_sorted.
            + apply le_all_trans_cons; try assumption.
              apply head_of_sorted_le_all. exact ys_is_sorted.
        }
      * { (* x > y *) apply leb_complete_conv in neq as neq'.
          rewrite merge2_gt; try assumption.
          apply cons_is_sorted.
          - apply IHys; assumption.
          - apply le_all_merge.
            + apply le_all_trans_cons.
              * apply Nat.lt_le_incl. exact neq'.
              * apply head_of_sorted_le_all. exact xs_is_sorted.
            + apply head_of_sorted_le_all. exact ys_is_sorted.
        }
Qed.

Theorem merge_pairs_is_sorted (xss: list (list nat)):
  all_is_sorted xss -> all_is_sorted (merge_pairs xss).
Proof.
  apply (list_ind2 (fun xss => all_is_sorted xss -> all_is_sorted (merge_pairs xss))); try auto.
  clear xss. intros xs1 xs2 xss IH H xs [xs_in_head | xs_in_rest].
  - subst xs. apply merge_is_sorted; apply H; simpl; auto.
  - apply IH.
    + intros ys ys_in_xss. apply H. simpl. auto.
    + exact xs_in_rest.
Qed.

Theorem merge_all_preserve_is_sorted (xss: list (list nat)):
  all_is_sorted xss -> Is_sorted (merge_all xss).
Proof.
  apply merge_all_ind; clear xss.
  - intuition. exact Nil_is_sorted.
  - intros xss xs eq H. apply H. simpl. auto.
  - intros xss xss' eq xss_struct IH H. subst xss'.
    apply IH, merge_pairs_is_sorted, H.
Qed.

Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort. apply merge_all_preserve_is_sorted, split_all_is_sorted.
Qed.

(* === merge_sort contains same elements in the same count === *)
Theorem split_all_concat (xs: list nat): xs = concat (split_all xs).
Proof.
  induction xs as [|x xs' IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Theorem merge_perm (xs ys: list nat): Permutation (xs ++ ys) (merge xs ys).
Proof.
  generalize dependent ys. induction xs as [|x xs' IHxs]; intro ys.
  - (* xs = [] *) simpl. destruct ys; auto.
  - (* xs = x :: xs' *) induction ys as [|y ys' IHys].
    + (* ys = [] *) simpl. rewrite app_nil_r. apply Permutation_refl.
    + (* ys = y :: ys' *)
      destruct (x <=? y) eqn:neq.
      * { (* x <= y *) apply leb_complete in neq as neq'.
          rewrite merge2_le; try exact neq'.
          rewrite <- app_comm_cons. apply perm_skip. apply IHxs.
        }
      * { (* x > y *) apply leb_complete_conv in neq as neq'.
          rewrite merge2_gt; try exact neq'.
          apply Permutation_trans with (l' := y :: (x :: xs') ++ ys').
          - apply Permutation_sym. apply Permutation_middle.
          - apply perm_skip, IHys.
        }
Qed.  
        
Theorem merge_pairs_perm (xss: list (list nat)): Permutation (concat xss) (concat (merge_pairs xss)).
Proof.
  apply (list_ind2 (fun xss: list (list nat) => Permutation (concat xss) (concat (merge_pairs xss))));
    clear xss.
  - simpl. apply Permutation_refl.
  - intro xs. simpl. rewrite app_nil_r. apply Permutation_refl.
  - intros xs1 xs2 xss IH. simpl. rewrite app_assoc. apply Permutation_app.
    + apply merge_perm.
    + exact IH.
Qed.
        
Theorem merge_all_perm (xss: list (list nat)): Permutation (concat xss) (merge_all xss).
Proof.
  apply merge_all_ind; clear xss.
  - auto.
  - intros xss xs eq. subst xss. simpl. rewrite app_nil_r. apply Permutation_refl.
  - intros xss xss' eq H IH. subst xss'.
    apply Permutation_trans with (l' := concat (merge_pairs xss)).
    + apply merge_pairs_perm.
    + exact IH.
Qed.

Theorem merge_sort_perm (xs: list nat): Permutation xs (merge_sort xs).
Proof.
  unfold merge_sort. apply Permutation_trans with (l' := (concat (split_all xs))).
  - rewrite <- split_all_concat. apply Permutation_refl.
  - apply merge_all_perm.
Qed.

(* === Preserve legth === *)
Theorem merge_sort_preserve_lenght (xs: list nat): length (merge_sort xs) = length xs.
Proof.
  symmetry. apply Permutation_length. apply merge_sort_perm.
Qed.

(* see Permutation_in and Permutation_ind_bis *)
