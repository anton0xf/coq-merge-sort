
module Nat =
 struct
 end

(** val merge : int list -> int list -> int list **)

let rec merge xs ys =
  let rec aux ys0 =
    match xs with
    | [] -> ys0
    | x::xs' ->
      (match ys0 with
       | [] -> xs
       | y::ys' -> if (<=) x y then x::(merge xs' ys0) else y::(aux ys'))
  in aux ys

(** val split_all : int list -> int list list **)

let rec split_all = function
| [] -> []
| x::xs' -> (x::[])::(split_all xs')

(** val merge_pairs : int list list -> int list list **)

let rec merge_pairs = function
| [] -> []
| xs1::l ->
  (match l with
   | [] -> xs1::[]
   | xs2::xs' -> (merge xs1 xs2)::(merge_pairs xs'))

(** val merge_all : int list list -> int list **)

let rec merge_all = function
| [] -> []
| l::l0 ->
  (match l0 with
   | [] -> l
   | l1::l2 -> merge_all (merge_pairs (l::(l1::l2))))

(** val merge_sort : int list -> int list **)

let merge_sort xs =
  merge_all (split_all xs)
