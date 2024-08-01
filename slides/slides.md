<!--
footer: https://github.com/anton0xf/coq-merge-sort 
header: Антон Стеканов -->

# Доказательство корректности программ
формальная верификация с использованием [Coq](https://en.wikipedia.org/wiki/Coq_(software)) \
* disclaimer
* методы проверки корректности программ
* почему формальная верификация
* пример merge sort
* как это работает

---

# Как проверить программу?
* вручную
* Unit tests
* другие автотесты
* доказательство корректности
* формальная верификация доказательств
* автоматическая верификация и доказательства

---

# Автотестов не достаточно?
* [Nearly All Binary Searches and Mergesorts are Broken](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/)
  * [A bug was found in Java after almost 9 years of hiding](https://dev.to/matheusgomes062/a-bug-was-found-in-java-after-almost-9-years-of-hiding-2d4k) \
    [JDK-5045582](https://bugs.java.com/bugdatabase/view_bug?bug_id=5045582): (coll) binarySearch() fails for size larger than 1<<30
* [The Java standard library implementation of Timsort has a bug](https://www.reddit.com/r/programming/comments/9btk1d/the_java_standard_library_implementation_of/) \
  [JDK-8203864](https://bugs.openjdk.org/browse/JDK-8203864): Execution error in Java's Timsort

---

# Merge sort
[Merge sort](https://en.wikipedia.org/wiki/Merge_sort) - [Сортировка слиянием](https://ru.wikipedia.org/wiki/%D0%A1%D0%BE%D1%80%D1%82%D0%B8%D1%80%D0%BE%D0%B2%D0%BA%D0%B0_%D1%81%D0%BB%D0%B8%D1%8F%D0%BD%D0%B8%D0%B5%D0%BC)
* Реализуем в [Coq](https://en.wikipedia.org/wiki/Coq_(software))
* Верифицируем там же
* Извлекаем в OCaml модуль
* Запускаем

---

# Merge sort
[Merge sort](https://en.wikipedia.org/wiki/Merge_sort)
![width:500px](./img/merge.gif)

---

# [Coq](https://en.wikipedia.org/wiki/Coq_(software))
* [proof assistant](https://en.wikipedia.org/wiki/Proof_assistant) \
  [инструмент интерактивного доказательства теорем](https://ru.wikipedia.org/wiki/%D0%98%D0%BD%D1%81%D1%82%D1%80%D1%83%D0%BC%D0%B5%D0%BD%D1%82_%D0%B8%D0%BD%D1%82%D0%B5%D1%80%D0%B0%D0%BA%D1%82%D0%B8%D0%B2%D0%BD%D0%BE%D0%B3%D0%BE_%D0%B4%D0%BE%D0%BA%D0%B0%D0%B7%D0%B0%D1%82%D0%B5%D0%BB%D1%8C%D1%81%D1%82%D0%B2%D0%B0_%D1%82%D0%B5%D0%BE%D1%80%D0%B5%D0%BC)
* язык программирования с зависимыми типами с поддержкой тактик
* основан на CIC (calculus of inductive constructions)
  разработанном [Thierry Coquand](https://ru.wikipedia.org/wiki/%D0%9A%D0%BE%D0%BA%D0%B0%D0%BD,_%D0%A2%D1%8C%D0%B5%D1%80%D1%80%D0%B8)
* разработан во Франции при участии [INRIA](https://ru.wikipedia.org/wiki/INRIA "фр. Institut national de recherche en informatique et en automatique, Национальный институт исследований в информатике и автоматике") в 1989г.

---

# Merge sort на Haskell
https://stackoverflow.com/a/52896140
```haskell
sort :: (Ord a) => [a] -> [a]
sort = mergeAll . map (: [])
  where
    mergeAll [] = []
    mergeAll [xs] = xs
    mergeAll xss  = mergeAll (mergePairs xss)

    mergePairs (xs : ys : xss) = merge xs ys : mergePairs xss
    mergePairs xss = xss
```

---

# Каррирование / [curring](https://en.wikipedia.org/wiki/Currying)
```java
String rep(String x, int n) {
    return x.repeat(n);
}
```
```java
BiFunction<String, Integer, String> rep =
    (String x, Integer n) -> x.repeat(n);
```
```java
rep("q", 4) // => "qqqq"
```

---
# Каррирование / [curring](https://en.wikipedia.org/wiki/Currying)
```java
String rep(String x) {
    return (Integer n) -> x.repeat(n);
}
```
```java
Function<String, Function<Integer, String>> rep =
    (String x) -> (Integer n) -> x.repeat(n)
```
```java
rep("q")(4) // => "qqqq"
```
---
# Каррирование / [curring](https://en.wikipedia.org/wiki/Currying)

```haskell
rep :: String -> Int -> String
rep s n = concat (replicate n s)
```
---

# Моя версия на Coq/Gallina
https://github.com/anton0xf/coq-merge-sort/blob/main/Merge.v
```coq
Definition merge_sort (xs: list nat): list nat :=
  merge_all (split_all xs).

Compute merge_sort [2; 3; 1; 5; 4; 6; 4].
(* = Some [1; 2; 3; 4; 4; 5; 6] : list nat *)
```
---

# split_all
```coq
Fixpoint split_all (xs: list nat): list (list nat) :=
  match xs with
  | nil => nil
  | x :: xs' => [x] :: split_all xs'
  end.

Compute split_all [1;2;3].
(* = [[1]; [2]; [3]] : list (list nat) *)
```

---

# merge
```coq
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
```

---

# merge (check)
```coq
Example merge_nil_l: merge [] [1; 2] = [1; 2].
Proof. trivial. Qed.

Example merge_nil_r: merge [1] [] = [1].
Proof. trivial. Qed.

Example merge_ex: merge [1; 3; 4] [0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.
```

---

# Свойства
* сортирует
* не теряет и не добавляет элементы

---

# Сортирует?
```coq
Inductive Is_sorted: list nat -> Prop :=
| Nil_is_sorted: Is_sorted []
| Single_is_sorted (x: nat): Is_sorted [x]
| Cons2_is_sorted (x1 x2: nat) (xs: list nat):
  x1 <= x2 /\ Is_sorted (x2 :: xs) -> Is_sorted (x1 :: x2 :: xs).
```
---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
  apply split_all_is_sorted.
Qed.
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
```
```
  xs : list nat
  ============================
  Is_sorted (merge_sort xs)
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
```
```
  xs : list nat
  ============================
  Is_sorted (merge_sort xs)
```
```coq
Definition merge_sort (xs: list nat): list nat :=
  merge_all (split_all xs).
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
```
```
  xs : list nat
  ============================
  Is_sorted (merge_all (split_all xs))
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
```
```
  xs : list nat
  ============================
  Is_sorted (merge_all (split_all xs))
```
```coq
Theorem merge_all_preserve_is_sorted (xss: list (list nat)):
  all_is_sorted xss -> Is_sorted (merge_all xss).
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
```
```
  xs : list nat
  ============================
  all_is_sorted (split_all xs)
```
```coq
Theorem merge_all_preserve_is_sorted (xss: list (list nat)):
  all_is_sorted xss -> Is_sorted (merge_all xss).
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
```
```
  xs : list nat
  ============================
  all_is_sorted (split_all xs)
```
```coq
Theorem split_all_is_sorted (xs: list nat): all_is_sorted (split_all xs).
```

---
# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
  apply split_all_is_sorted.
```
```
No more goals.
```

---

# merge_sort_is_sorted
```coq
Theorem merge_sort_is_sorted (xs: list nat): Is_sorted (merge_sort xs).
Proof.
  unfold merge_sort.
  apply merge_all_preserve_is_sorted.
  apply split_all_is_sorted.
Qed.
```

---

# split_all_is_sorted
```coq
Theorem split_all_is_sorted (xs: list nat): all_is_sorted (split_all xs).
Proof.
  induction xs as [|x xs' IH].
  - simpl. intros ys H. destruct H.
  - simpl. intros ys [H | H].
    + subst ys. apply Single_is_sorted.
    + apply IH, H.
Qed.
```

---

# Извлечение
```coq
Require Import Arith.
Require Import List.
Import ListNotations.

From Demo Require Import Merge.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat => "int" [ "0" "(+) 1" ].
Extract Inlined Constant leb => "(<=)".
Set Extraction Output Directory "ocaml".
Extraction "merge_sort.ml" merge_sort.
```

---

# Результат
```ocaml
let rec merge xs ys =
  let rec aux ys0 =
    match xs with
    | [] -> ys0
    | x::xs' ->
      (match ys0 with
       | [] -> xs
       | y::ys' -> if (<=) x y then x::(merge xs' ys0) else y::(aux ys'))
  in aux ys

let rec split_all = function
| [] -> []
| x::xs' -> (x::[])::(split_all xs')

let rec merge_pairs = function
| [] -> []
| xs1::l ->
  (match l with
   | [] -> xs1::[]
   | xs2::xs' -> (merge xs1 xs2)::(merge_pairs xs'))

let rec merge_all = function
| [] -> []
| l::l0 ->
  (match l0 with
   | [] -> l
   | l1::l2 -> merge_all (merge_pairs (l::(l1::l2))))

let merge_sort xs =
  merge_all (split_all xs)

```

---

# Результат
```ocaml
(** val merge_sort : int list -> int list **)
let merge_sort xs =
  merge_all (split_all xs)
```
```coq
Definition merge_sort (xs: list nat): list nat :=
  merge_all (split_all xs).
```
---

# Результат
```ocaml
(** val split_all : int list -> int list list **)
let rec split_all = function
| [] -> []
| x::xs' -> (x::[])::(split_all xs')
```
```coq
Fixpoint split_all (xs: list nat): list (list nat) :=
  match xs with
  | nil => nil
  | x :: xs' => [x] :: split_all xs'
  end.
```
---

# Запуск
`merge_demo.ml`
```ocaml
open Merge_sort

let () = [5;3;4;2;5;1] 
         |> merge_sort
         |> List.map string_of_int 
         |> String.concat ";" 
         |> print_string
```
```sh
$ ./merge_demo
1;2;3;4;5;5
```
[F#](https://try.fsharp.org/#?code=LAKAtg9gJgrgNgUwAQDkCGAXJBeUSDOGATjAMYZ4IB2UooAFAFSNIBuacSYCRA5sgC4kASypY4wwkgC0APhFikEqXIXjJWZgEo6IRFiIJSXHvyQAPfEgCeV3CCRKEBo0jQxzN-AAYceR1yYpAAWFlYA7sIYwf6OAD5IANoAujLytt6xSAnmAgKWAORpSPRgQaEZSJHRWQF19dlJqaqWtQ0NCdZ5tkWqwgBmJUgAPNhIWhY2SNHUFnmlpsiFXt4TCHD4yF0C9O6ePVo6DgpuHl66TCzsnPgADhIYAPocnEKi6iry70oaP1Laun0SEMxjuD2ecE4Y36MCo5GEECooASKWKKWRc3y+F68nouQEKS08zBUQhnEKRwYzDYHBMfAQj1uaGERCsb0Uyg+WD6HN+nKQAJAoCBILp-EZzNZOCQMLhGARSJAKOa8nRSrCAEY8pxVKVykoqlEYsd2nVlcVLFqCck2u0cvgAEx5Za67j0zVhB1EnZu8VMllWCmUkCXGmcX0Ml5Idlcv7cr68-6MYMi1wRsnS2XwxEY1GqNUJODa3yu-VwXzVY2ms1NYpwW31QtWuAO4rpqMLekSgMlIs7ODNr2HYOh65ihn4CBELAxuPFb78wXC5zjx6T6dhaX+duQkokp5Rywplf0CZjRIAVgA3ABmK8AFivDqv141qTi8nT66wH6QDaQAAyGgAHRlLcBDEKIvDZPIADKkFULwwGkIipCYEgABEV4YTBSC3EQ7yDBhACk+AADpUBhQA&html=DwCwLgtgNgfAsAKAAQqaApgQwCb2ag4CdMTJcMABwFp0BHAVwEsA3AXgCIBhAewDsw6AdQAqAT0roOSAMb9BAzoIAeYAPThoAbhkhMAJwDOJNgzAAzagA4OeQhqy5EhAEY9sYu6mBq3HvD6asEA&css=Q)

---

# А если императивные?

---

# Как это работает?
* Типизированное λ-исчисление
* [CIC](https://en.wikipedia.org/wiki/Calculus_of_constructions) - Calculus of Inductive Constructions
* Интуиционистская (конструктивная) логика (no LEM included)
* Соответствие Карри-Ховарда - Curry–Howard correspondence ([ru](https://ru.wikipedia.org/wiki/%D0%A1%D0%BE%D0%BE%D1%82%D0%B2%D0%B5%D1%82%D1%81%D1%82%D0%B2%D0%B8%D0%B5_%D0%9A%D0%B0%D1%80%D1%80%D0%B8_%E2%80%94_%D0%A5%D0%BE%D0%B2%D0%B0%D1%80%D0%B4%D0%B0), [en](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence))
* BHK - [Brouwer–Heyting–Kolmogorov interpretation](https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)

---

# BHK
[Brouwer–Heyting–Kolmogorov interpretation](https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)
* доказательство `A /\ B` - это пары из доказательств: `<A, B>`
* доказательство `A \/ B` - это пара `<0, A>` или `<1, B>`
* существование - доказывается предоставлением объекта \
  и доказательства для него: `∃ x, P(x)` ≡ `<x, P(x)>`
* верность для всех - функция из произвольного \
  в доказательство для него: `∀ x, P(x)` ≡ `x => f(x)`
* доказательство `A -> B` - это функция, которая стоит из произвольного доказательства 

---

# Curry–Howard
* доказательство - вычисление
* x - свидетельство A ≡ `x: A`
* `A -> B` ≡ `(x: A) => f(x) : B`
* `A` доказуемо ≡ `_ : A`
* `A /\ B` - это пары из доказательств: `<A, B>`
* `∀ x, P(x)` ≡ `(x: A) => f(x) : P(x)`

---

# Зависимые типы
`∀ x, P(x)` ≡ `(x: A) => f(x) : P(x)`

---

# Куда дальше?
* [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
* [Coq in a Hurry](https://cel.hal.science/inria-00001173v4/file/coq-hurry.pdf)
* [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/)
* [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) - Types and Programming Languages

---

# Спасибо за внимание!

QR-CODE ???
