From Coq Require Export
  Lia
  List
  String.
Export ListNotations.
From Lang Require Import
  Count
  Invert
  Remove.

(* TODO: This needs to be deterministic. If not, free variables are nondeterministic, which is disastrous. *)
(* Partition a context into types (which allow structural rules) and values (which don't). *)
Inductive Partition {T} : list T -> list T -> list T -> Prop :=
  | PartitionDone : forall src,
      Partition src [] src
  | PartitionCopy : forall x src hi lo n,
      Count x src (S n) ->
      Count x lo (S n) ->
      Partition src hi lo ->
      Partition src (x :: hi) lo
  | PartitionMove : forall x src src' hi lo nsrc nlo,
      Count x src nsrc ->
      Count x lo nlo ->
      nsrc > nlo ->
      Partition src' hi lo ->
      Remove x src src' ->
      Partition src (x :: hi) lo
  .
Arguments Partition {T} src hi lo.
Ltac partition_done := apply PartitionDone.
Ltac partition_move := eapply PartitionMove; [autocount | autocount | lia | | repeat constructor; intro; discriminate].
Ltac partition_copy := eapply PartitionCopy; [autocount | autocount |].
Ltac partition_step := first [partition_done | partition_copy | partition_move].
Ltac partition := first [partition_done | first [partition_copy | partition_move]; partition].

Example partition_12345 : Partition [1;2;3;4;5] [1;1;1;1;1;1;4;2;3;3] [1;3;5]. Proof. partition. Qed.

(* not efficient at all but not a problem right now *)
Fixpoint partition_src_with {T} (f : T -> T -> bool) hi lo :=
  match hi with
  | [] => lo
  | hd :: tl =>
      let recursed := partition_src_with f tl lo in
      if (existsb (f hd) tl || existsb (f hd) lo)%bool then recursed else hd :: recursed
  end.

Lemma existsb_in : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  Bool.reflect (In x li) (existsb (f x) li).
Proof.
  intros. generalize dependent f. generalize dependent x. induction li; intros; simpl in *. { constructor. intros []. }
  destruct (X x a). { subst. constructor. left. reflexivity. }
  destruct (IHli x f X); constructor. { right. assumption. }
  intros [C | C]. { subst. apply n. reflexivity. } apply n0. assumption.
Qed.

Lemma existsb_in_iff : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  (In x li <-> existsb (f x) li = true).
Proof.
  intros. destruct (existsb_in f x li X); split; intros.
  { reflexivity. } { assumption. } { contradiction. } { discriminate. }
Qed.

Lemma existsb_in_iff_not : forall {T} f x li,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  (~In x li <-> existsb (f x) li = false).
Proof.
  intros. destruct (existsb_in f x li X); split; intros.
  { contradiction. } { discriminate. } { reflexivity. } { assumption. }
Qed.

Theorem in_partition_src : forall {T} x (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  In x (partition_src_with f hi lo) <-> (In x hi \/ In x lo).
Proof.
  split; intros.
  - generalize dependent x. generalize dependent f. generalize dependent lo.
    induction hi; intros; simpl in *. { right. assumption. }
    apply or_assoc. destruct (existsb_in f a hi X); simpl in *. { right. eapply IHhi. { apply X. } assumption. }
    destruct (existsb_in f a lo X). { right. eapply IHhi. { apply X. } assumption. }
    destruct H. { left. assumption. } apply IHhi in H; [| apply X]. right. assumption.
  - generalize dependent x. generalize dependent f. generalize dependent lo.
    induction hi; intros; simpl in *. { destruct H. { destruct H. } assumption. }
    apply or_assoc in H. destruct H; subst.
    + destruct (existsb_in f x hi X); simpl in *. { apply IHhi; [| left]; assumption. }
      destruct (existsb_in f x lo X); simpl in *. { apply IHhi; [| right]; assumption. }
      left. reflexivity.
    + destruct (existsb_in f a hi X); simpl in *. { apply IHhi; assumption. }
      destruct (existsb_in f a lo X); simpl in *. { apply IHhi; assumption. }
      destruct (X a x). { left. assumption. } right. apply IHhi; assumption.
Qed.

Theorem count_partition_src : forall {T} x f hi lo,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  count f x (partition_src_with f hi lo) = (
    match count f x lo with
    | O =>
        match count f x hi with
        | O => O
        | S _ => 1
        end
    | S n =>
        S n
    end).
Proof.
  intros T x f hi. generalize dependent x. generalize dependent f. induction hi; intros; simpl in *.
  - induction lo; simpl in *. { constructor. }
    destruct (X x a); [rewrite count_S |]; destruct (count_acc 0 f x lo); reflexivity.
  - destruct (existsb_in f a hi X); simpl in *.
    + destruct (X x a); [| apply IHhi; assumption]. subst. rewrite count_S.
      rewrite (IHhi f a lo X). eapply existsb_in_iff in i; [| apply X].
      destruct (count_existsb f a hi X); [| discriminate i]. simpl in n.
      destruct (count_acc 0 f a hi). { contradiction n. reflexivity. } reflexivity.
    + destruct (existsb_in f a lo X); simpl in *.
      * destruct (X x a); [| apply IHhi; apply X]. subst. rewrite count_S.
        rewrite (IHhi f a lo X). eapply existsb_in_iff in i; [| apply X].
        destruct (count_existsb f a lo X); [| discriminate i]. simpl in n0.
        destruct (count_acc 0 f a lo). { contradiction n0. reflexivity. } reflexivity.
      * eapply existsb_in_iff_not in n; [| apply X]. eapply existsb_in_iff_not in n0; [| apply X].
        destruct (count_existsb f a lo X); try discriminate n0. destruct (count_existsb f a hi X); try discriminate n.
        simpl in *. destruct (count_acc 0 f a lo) eqn:El; try (contradiction n1; intro C; discriminate C).
        destruct (count_acc 0 f a hi) eqn:Eh; try (contradiction n2; intro C; discriminate C).
        destruct (X x a). { subst. repeat rewrite count_S. rewrite IHhi; [| apply X]. rewrite El. rewrite Eh. reflexivity. }
        apply IHhi. apply X.
Qed.

(*
Theorem partition_src_works : forall {T} (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  Partition (partition_src_with f hi lo) hi lo.
Proof.
  induction hi; intros; simpl in *. { constructor. }
  destruct (count_existsb f a hi X); simpl in *.

  destruct (count_existsb f a hi); [apply X | |]; simpl in *.
  - destruct (count_acc 0 f a hi) eqn:Eh. { contradiction n. reflexivity. } clear n.
    eapply PartitionCopy; [| | apply IHhi; apply X]; (eapply reflect_count; [apply X |]).
    + rewrite count_partition_src; [| apply X]. simpl. rewrite Eh. assert (A :
        match count_acc 0 f a lo with O => 1 | S n => S n end =
        S match count_acc 0 f a lo with O => O | S n => n end);
      [destruct (count_acc 0 f a lo); reflexivity |]. apply A.
    + simpl. destruct (count_acc 0 f a lo) eqn:El; [| reflexivity]. admit.
  - destruct (count_acc 0 f a hi) eqn:Eh; [| contradiction n; intro C; discriminate C]. clear n.
    destruct (count_existsb f a lo). { apply X. }

    remember (count_acc 0 f a lo) as nlo eqn:Enlo. symmetry in Enlo. destruct (PeanoNat.Nat.eqb_spec (S n0) nlo).
    + subst. eapply PartitionCopy; [| | apply IHhi; apply X]; (eapply reflect_count; [apply X |]).
      2: { symmetry. apply e. } rewrite count_partition_src; [| apply X]. simpl. rewrite Eh. rewrite <- e. reflexivity.
    + eapply PartitionMove.
      * eapply reflect_count. { apply X. } apply count_partition_src. apply X.
      * eapply reflect_count. { apply X. } shelve.
      * simpl. rewrite Eh. rewrite Enlo. shelve.
      * apply IHhi. apply X.
      * 

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

Theorem partition_deterministic : forall {T} src src' hi lo,
  @Partition T src hi lo ->
  Partition src' hi lo ->
  src = src'.
Proof.
  intros. generalize dependent src'. induction H; intros.
  - (* PartitionDone *)
    invert H0. reflexivity.
  - (* PartitionCopy *)
    invert H1.
    + (* PartitionCopy *)
      apply IHPartition; assumption.
    + (* PartitionMove *)
      invert H5.
      * invert H.
      apply IHPartition. invert H5.
      * invert H.
      generalize dependent src. generalize dependent hi. generalize dependent lo. induction H7; intros; simpl in *.
      * apply IHPartition. apply PartitionCopy.
  - (* PartitionMove *)
    invert H1.
    + (* PartitionCopy *)
      apply IHPartition.
Qed.

Theorem partition_map_fst : forall {A B} src hi lo,
  @Partition (A * B) src hi lo ->
  Partition (map fst src) (map fst hi) (map fst lo).
Proof.
  intros. induction H. { constructor. }
  - destruct x. simpl. constructor. { assumption. } eapply in_map_fst. apply H0.
  - destruct x. simpl. eapply PartitionMove. { apply IHPartition. } eapply remove_map_fst. apply H0.
Qed.
*)
