From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

(* Implementation of merge sort  *)
Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: t =>
      let '(xs, ys) := split t in
      (a :: xs, b :: ys)
  end.

Fixpoint merge (left : list nat) (right : list nat) : list nat :=
  let fix merge_right (right : list nat) : list nat :=
    match left, right with
    | [], _ => right
    | _, [] => left
    | a :: left', b :: right' =>
        if Nat.leb a b
        then a :: merge left' right
        else b :: merge_right right'
    end
  in merge_right right.

(* Fuel makes termination structural; length l bounds the recursion depth. *)
Fixpoint merge_sort_fuel (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
      match l with
      | [] => []
      | [a] => [a]
      | _ =>
          let '(xs, ys) := split l in
          merge (merge_sort_fuel fuel' xs) (merge_sort_fuel fuel' ys)
      end
  end.

Definition merge_sort (l : list nat) : list nat := merge_sort_fuel (length l) l.
