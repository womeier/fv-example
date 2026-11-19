From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From SortingExample Require Import SortSpec MergeSort.
Import ListNotations.

Example sort_example : merge_sort [3; 1; 4; 1; 5; 2] = [1; 1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Example sort_empty : merge_sort [] = [].
Proof. reflexivity. Qed.

Lemma permutation_refl : forall l, permutation l l.
Proof.
  induction l; constructor; assumption.
Qed.

Lemma permutation_sym : forall l r, permutation l r -> permutation r l.
Proof.
  intros l r H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor.
  - eapply perm_trans; eauto.
Qed.

Lemma permutation_app : forall l l' r r',
    permutation l l' -> permutation r r' ->
    permutation (l ++ r) (l' ++ r').
Proof.
  intros l l' r r' H Hr.
  assert (Hleft : permutation (l ++ r) (l' ++ r)).
  { induction H; simpl.
    - apply permutation_refl.
    - constructor; assumption.
    - constructor.
    - eapply perm_trans; eauto. }
  eapply perm_trans; [exact Hleft |].
  clear Hleft H l.
  induction l'; simpl; [exact Hr | constructor; assumption].
Qed.

Lemma permutation_move : forall x l r,
    permutation (l ++ x :: r) (x :: l ++ r).
Proof.
  intros x l; induction l as [|a l IH]; intros r; simpl.
  - apply permutation_refl.
  - eapply perm_trans.
    + apply perm_skip, IH.
    + apply perm_swap.
Qed.

Lemma split_properties : forall l xs ys,
    split l = (xs, ys) ->
    permutation (xs ++ ys) l /\ length xs + length ys = length l.
Proof.
  fix IH 1.
  intros [|a [|b t]] xs ys H; simpl in H.
  - inversion H; subst; simpl; split; constructor.
  - inversion H; subst; simpl; split; [apply permutation_refl | reflexivity].
  - destruct (split t) as [us vs] eqn:E.
    inversion H; subst; simpl.
    destruct (IH t us vs E) as [Hp Hl].
    split.
    + apply perm_skip.
      eapply perm_trans; [apply permutation_move |].
      apply perm_skip; exact Hp.
    + simpl in *; lia.
Qed.

Lemma merge_permutation : forall l r,
    permutation (merge l r) (l ++ r).
Proof.
  induction l as [|a l IH]; intros r;
    [destruct r; simpl; apply permutation_refl |].
  induction r as [|b r IHr]; [simpl; rewrite app_nil_r; apply permutation_refl |].
  simpl; destruct (a <=? b).
  - apply perm_skip, IH.
  - eapply perm_trans.
    + apply perm_skip, IHr.
    + apply permutation_sym; exact (permutation_move b (a :: l) r).
Qed.

Lemma sorted_tail : forall a l, sorted (a :: l) -> sorted l.
Proof.
  intros a l H; inversion H; subst; [constructor | assumption].
Qed.

Lemma sorted_lower : forall l, sorted l -> forall a,
    (match l with [] => True | b :: _ => a <= b end) ->
    Forall (fun b => a <= b) l.
Proof.
  intros l H; induction H; intros x Hx.
  - constructor.
  - constructor; [exact Hx | constructor].
  - constructor; [exact Hx | apply IHsorted; simpl; lia].
Qed.

Lemma sorted_prepend : forall a l,
    Forall (fun b => a <= b) l -> sorted l -> sorted (a :: l).
Proof.
  intros a [|b l] Hb Hs; [constructor |].
  inversion Hb; subst; constructor; assumption.
Qed.

Lemma merge_lower : forall a l r,
    Forall (fun b => a <= b) l ->
    Forall (fun b => a <= b) r ->
    Forall (fun b => a <= b) (merge l r).
Proof.
  intros a l; induction l as [|b l IH]; intros r Hl Hr;
    [destruct r; exact Hr |].
  induction r as [|c r IHr]; [exact Hl |].
  inversion Hl; inversion Hr; subst.
  simpl; destruct (b <=? c); constructor; auto.
Qed.

Lemma merge_sorted : forall l r,
    sorted l -> sorted r -> sorted (merge l r).
Proof.
  induction l as [|a l IH]; intros r Hl Hr; [destruct r; exact Hr |].
  induction r as [|b r IHr]; [exact Hl |].
  simpl; destruct (a <=? b) eqn:E; apply sorted_prepend.
  - apply merge_lower.
    + pose proof (sorted_lower (a :: l) Hl a (Nat.le_refl a)) as H.
      inversion H; assumption.
    + apply sorted_lower; [exact Hr | simpl; now apply Nat.leb_le].
  - apply IH; [eapply sorted_tail; exact Hl | exact Hr].
  - change (Forall (fun x => b <= x) (merge (a :: l) r)).
    apply merge_lower.
    + apply sorted_lower; [exact Hl | simpl; apply Nat.leb_gt in E; lia].
    + pose proof (sorted_lower (b :: r) Hr b (Nat.le_refl b)) as H.
      inversion H; assumption.
  - apply IHr; eapply sorted_tail; exact Hr.
Qed.

Lemma merge_sort_fuel_correct : forall fuel l,
    length l <= fuel ->
    sorted (merge_sort_fuel fuel l) /\ permutation (merge_sort_fuel fuel l) l.
Proof.
  induction fuel as [|fuel IH]; intros l Hlen.
  - destruct l; [split; constructor | simpl in Hlen; lia].
  - destruct l as [|a [|b t]].
    + split; constructor.
    + split; [constructor | apply permutation_refl].
    + simpl.
      destruct (split t) as [xs ys] eqn:E; simpl.
      destruct (split_properties t xs ys E) as [Hp Hsize].
      assert (Hx : length (a :: xs) <= fuel) by (simpl in *; lia).
      assert (Hy : length (b :: ys) <= fuel) by (simpl in *; lia).
      destruct (IH (a :: xs) Hx) as [Hsx Hpx].
      destruct (IH (b :: ys) Hy) as [Hsy Hpy].
      split; [apply merge_sorted; assumption |].
      eapply perm_trans; [apply merge_permutation |].
      eapply perm_trans; [apply permutation_app; eassumption |].
      apply perm_skip.
      eapply perm_trans; [apply permutation_move |].
      apply perm_skip; exact Hp.
Qed.

Theorem sort_correct_proof : sort_correct merge_sort.
Proof.
  intros l; unfold merge_sort; apply merge_sort_fuel_correct; lia.
Qed.

Print Assumptions sort_correct_proof.
