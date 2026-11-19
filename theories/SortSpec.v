From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

(* The specification: what it means for a list to be ordered. *)
Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_one : forall a, sorted [a]
| sorted_cons : forall a b t,
    a <= b -> sorted (b :: t) -> sorted (a :: b :: t).

(* Same elements, possibly in a different order. *)
Inductive permutation : list nat -> list nat -> Prop :=
| perm_nil : permutation [] []
| perm_skip : forall x l l',
    permutation l l' -> permutation (x :: l) (x :: l')
| perm_swap : forall x y l,
    permutation (y :: x :: l) (x :: y :: l)
| perm_trans : forall l l' l'',
    permutation l l' -> permutation l' l'' -> permutation l l''.

Definition sort_correct (algorithm : list nat -> list nat) : Prop :=
    forall l : list nat,
    sorted (algorithm l) /\ permutation (algorithm l) l.
