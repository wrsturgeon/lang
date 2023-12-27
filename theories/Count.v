From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  Invert.

Inductive Count {T} (x : T) : list T -> nat -> Prop :=
  | CountNil :
      Count x [] 0
  | CountEq : forall tl n,
      Count x tl n ->
      Count x (x :: tl) (S n)
  | CountNeq : forall hd tl n,
      Count x tl n ->
      x <> hd ->
      Count x (hd :: tl) n
  .
Ltac autocount := repeat constructor; intro; discriminate.

Example count_12345 : Count 2 [1;1;1;2;5;3;5;2;5;3;5;1;1;2] 3.
Proof. autocount. Qed.

Fixpoint count_acc acc {A B} (f : A -> B -> bool) x li :=
  match li with
  | [] => acc
  | hd :: tl => count_acc (if f x hd then S acc else acc) f x tl
  end.
Definition count := @count_acc O.
Arguments count/ {A B} f x li.

Lemma count_S : forall acc {A B} (f : A -> B -> bool) x li,
  count_acc (S acc) f x li = S (count_acc acc f x li).
Proof.
  intros. generalize dependent acc. generalize dependent A. induction li; intros; simpl in *. { reflexivity. }
  rewrite <- IHli. destruct (f x a); reflexivity.
Qed.

Theorem reflect_count : forall {T} li (f : T -> T -> bool) x n,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  count f x li = n <-> Count x li n.
Proof.
  induction li; intros; simpl in *. { split; intros. { subst. constructor. } inversion H. reflexivity. }
  destruct (X x a).
  - subst. rewrite count_S. split; intros.
    + subst. constructor. eapply IHli. { apply X. } reflexivity.
    + invert H; [| contradiction H4; reflexivity]. f_equal. apply IHli; assumption.
  - split; intros.
    + constructor; [eapply IHli; [apply X |] |]; assumption.
    + apply IHli. { assumption. } invert H. { contradiction n0. reflexivity. } assumption.
Qed.

Theorem count_deterministic : forall {T} x li m n,
  @Count T x li m ->
  Count x li n ->
  m = n.
Proof.
  intros. generalize dependent n. induction H; intros. { invert H0. reflexivity. }
  - invert H0. { f_equal. apply IHCount. assumption. } contradiction H5. reflexivity.
  - invert H1. { contradiction H0. reflexivity. } apply IHCount. assumption.
Qed.

Theorem count_existsb : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  Bool.reflect (count f x li <> 0) (existsb (f x) li).
Proof.
  intros. generalize dependent f. generalize dependent x.
  induction li; intros; simpl in *. { constructor. intro C. apply C. reflexivity. }
  destruct (f x a) eqn:Ef. { constructor. rewrite count_S. intro C. discriminate C. } apply IHli. assumption.
Qed.

Theorem count_existsb_true : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  count f x li <> 0 <-> existsb (f x) li = true.
Proof.
  intros. destruct (count_existsb f x li). { assumption. }
  - split; intros. { reflexivity. } { assumption. }
  - split; intros. { apply n in H as []. } { discriminate H. }
Qed.

Theorem count_existsb_false : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  count f x li = 0 <-> existsb (f x) li = false.
Proof.
  intros. destruct (count_existsb f x li). { assumption. }
  - split; intros. { apply n in H as []. } { discriminate H. }
  - split; intros. { reflexivity. } { destruct (count f x li). { reflexivity. } contradiction n. intro C. discriminate C. }
Qed.

Definition ap_fst_2 {A B C} : (A -> A -> C) -> A -> (A * B) -> C := fun f a pair =>
  let (b, _) := pair in f a b.
Arguments ap_fst_2 {A B C} f a pair.

Theorem count_map_fst : forall {K V} (f : K -> K -> bool) k (li : list (K * V)) acc,
  count_acc acc f k (map fst li) = count_acc acc (ap_fst_2 f) k li.
Proof.
  intros K V f k li. generalize dependent f. generalize dependent k. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl in *. destruct (f k k0); apply IHli.
Qed.

Theorem existsb_map_fst : forall {K V} (f : K -> K -> bool) k (li : list (K * V)),
  existsb (f k) (map fst li) = existsb (ap_fst_2 f k) li.
Proof.
  intros. generalize dependent f. generalize dependent k. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl in *. destruct (f k k0). { reflexivity. } apply IHli.
Qed.
