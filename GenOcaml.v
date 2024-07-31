Require Import Arith.
Require Import List.
Import ListNotations.

From Demo Require Import Merge.

(* === Extraction === *)
(* https://softwarefoundations.cis.upenn.edu/vfa-current/Extract.html *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "(+) 1" ].
Extract Inlined Constant leb => "(<=)".
(* Recursive Extraction merge_sort. *)
Set Extraction Output Directory "ocaml".
Extraction "merge_sort.ml" merge_sort.
