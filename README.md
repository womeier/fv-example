# Rocq Sorting Example

A minimal Rocq project containing merge sort with a correctness proof.

- [`theories/SortSpec.v`](theories/SortSpec.v): specification of sorting.
- [`theories/MergeSort.v`](theories/MergeSort.v): merge-sort implementation.
- [`theories/MergeSortCorrect.v`](theories/MergeSortCorrect.v#L159): the complete correctness proof of merge-sort

The `sorted` and `permutation` predicates are defined locally, but also available in the standard library. 

The files compile: the proof is complete and correct.
No additional axioms were introduced, `Print Assumptions sort_correct_proof.` reports `Closed under the global context`.


## Specification

The output must be nondecreasing and contain exactly the input elements,
including duplicates:

```coq
Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_one : forall a, sorted [a]
| sorted_cons : forall a b t,
    a <= b -> sorted (b :: t) -> sorted (a :: b :: t).

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
```

## Setup

With Nix installed and flakes enabled, build the project:

```sh
nix build
```
