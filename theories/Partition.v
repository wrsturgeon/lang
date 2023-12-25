From Coq Require Export
  List
  String.
Export ListNotations.
From Lang Require Import
  Invert
  Remove.

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

Example count_12345 : Count 2 [1;1;1;2;5;3;5;2;5;3;5;1;1;2] 3.
Proof. repeat constructor; intro C; discriminate C. Qed.

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

(* Partition a context into types (which allow structural rules) and values (which don't). *)
Inductive Partition {T} : list T -> list T -> list T -> Prop :=
  | PartitionDone : forall src,
      Partition src [] src
  | PartitionCopy : forall x src hi lo,
      Partition src hi lo ->
      In x src ->
      Partition src (x :: hi) lo
  | PartitionMove : forall x src src' hi lo,
      Partition src' hi lo ->
      Remove x src src' ->
      Partition src (x :: hi) lo
  .
Arguments Partition {T} src hi lo.
Ltac partition_done := apply PartitionDone.
Ltac partition_copy := eapply PartitionCopy; [| repeat (try (left; reflexivity); right)].
Ltac partition_move := eapply PartitionMove; [| repeat constructor].
(*
Ltac partition_done := apply PartitionDone.
Ltac partition_copy := eapply PartitionCopy; [| repeat (try (left; reflexivity); right); fail].
Ltac partition_move := eapply PartitionMove; [| repeat constructor; fail].
Ltac partition_step := first [partition_done | partition_copy | partition_move].
Ltac partition := first [partition_done | first [partition_copy | partition_move]; partition].
*)

Example partition_12345 : Partition [1;2;3;4;5] [1;1;1;1;1;1;4;2;3;3] [1;3;5].
Proof.
  partition_copy. partition_copy. partition_copy. partition_copy. partition_copy. partition_copy.
  partition_move. partition_move. partition_copy. partition_copy. partition_done.
Qed.

(* not efficient at all but not a problem right now *)
Fixpoint partition_src_with {T} (f : T -> T -> bool) hi lo :=
  match hi with
  | [] => lo
  | hd :: tl =>
      let recursed := partition_src_with f tl lo in
      if existsb (f hd) tl then recursed else hd :: recursed
  end.

Lemma existsb_eqb : forall x li,
  Bool.reflect (In x li) (existsb (eqb x) li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { constructor. intros []. }
  destruct (eqb_spec x a). { subst. constructor. left. reflexivity. }
  destruct (IHli x); constructor. { right. assumption. }
  intro C. destruct C. { subst. apply n. reflexivity. }
  apply n0. assumption.
Qed.

Theorem in_partition_src : forall {T} x (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  In x (partition_src_with f hi lo) <-> (In x hi \/ In x lo).
Proof.
  split; intros.
  - generalize dependent lo. generalize dependent x. induction hi; intros; simpl in *. { right. assumption. }
    destruct (existsb (f a) hi); [| destruct H; [subst; left; left; reflexivity |]];
    apply or_assoc; right; apply IHhi; assumption.
  - generalize dependent lo. generalize dependent x. induction hi; intros; simpl in *. { repeat destruct H. assumption. }
    apply or_assoc in H. destruct (existsb (f a) hi) eqn:E; [destruct H | destruct H; [subst; left; reflexivity | right]];
    try (apply IHhi; assumption). subst. clear IHhi. generalize dependent f. generalize dependent x. generalize dependent lo.
    induction hi; intros; simpl in *. { discriminate E. } apply Bool.orb_true_iff in E. destruct E.
    + destruct (X x a); invert H. destruct (existsb (f a) hi) eqn:Ea. { apply IHhi; assumption. } left. reflexivity.
    + destruct (existsb (f a) hi); [| right]; apply IHhi; assumption.
Qed.

Theorem partition_src_works : forall {T} (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  Partition (partition_src_with f hi lo) hi lo.
Proof.
  induction hi; intros; simpl in *. { constructor. }
  destruct (existsb (f a) hi) eqn:E; [| eapply PartitionMove; [apply IHhi; assumption | constructor]].
  constructor. { apply IHhi. assumption. } apply in_partition_src. { assumption. }
  left. clear lo. clear IHhi. generalize dependent f. generalize dependent a.
  induction hi; intros; simpl in *. { discriminate E. }
  apply Bool.orb_true_iff in E. destruct E. { destruct (X a0 a). { left. symmetry. assumption. } discriminate H. }
  right. eapply IHhi. { apply X. } assumption.
Qed.

Lemma in_map_fst : forall {A B} a b li,
  @In (A * B) (a, b) li ->
  In a (map fst li).
Proof.
  intros. generalize dependent a. generalize dependent b. induction li; intros; destruct H.
  - invert H. left. reflexivity.
  - destruct a. right. eapply IHli. apply H.
Qed.

Theorem partition_map_fst : forall {A B} src hi lo,
  @Partition (A * B) src hi lo ->
  Partition (map fst src) (map fst hi) (map fst lo).
Proof.
  intros. induction H. { constructor. }
  - destruct x. simpl. constructor. { assumption. } eapply in_map_fst. apply H0.
  - destruct x. simpl. eapply PartitionMove. { apply IHPartition. } eapply remove_map_fst. apply H0.
Qed.
