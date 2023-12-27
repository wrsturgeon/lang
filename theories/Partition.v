From Coq Require Export
  Lia
  List
  String.
Export ListNotations.
From Lang Require Import
  Count
  InTactics
  Invert
  Remove.

(* Partition a context into types (which allow structural rules) and values (which don't). *)
Inductive Partition {T} : list T -> list T -> list T -> Prop :=
  | PartitionDone : forall src,
      Partition src [] src
  | PartitionCpHi : forall x src hi lo,
      In x hi ->
      Partition src hi lo ->
      Partition src (x :: hi) lo
  | PartitionCpLo : forall x src hi lo,
      ~In x hi ->
      In x lo ->
      Partition src hi lo ->
      Partition src (x :: hi) lo
  | PartitionMove : forall x src hi lo,
      ~In x hi ->
      ~In x src ->
      Partition src hi lo ->
      Partition (x :: src) (x :: hi) lo
  .
Arguments Partition {T} src hi lo.
Ltac partition_done := apply PartitionDone.
Ltac partition_copy_hi := eapply PartitionCpHi; [auto_in |].
Ltac partition_copy_lo := eapply PartitionCpLo; [intros C; not_in C | auto_in |].
Ltac partition_move := eapply PartitionMove; [intros C; not_in C | intros C; not_in C |].
Ltac partition_step := first [partition_done | partition_copy_hi | partition_copy_lo | partition_move].
Ltac try_partition := repeat partition_step.
Ltac partition := first [partition_done | first [partition_copy_hi | partition_copy_lo | partition_move]; partition].

Example partition_12345 : Partition [4;2;1;3;5] [1;1;1;1;1;1;4;2;3;2;2;3] [1;3;5]. Proof. partition. Qed.

Theorem partition_src_app_lo : forall {T} src hi lo,
  @Partition T src hi lo ->
  exists pre, src = pre ++ lo.
Proof.
  intros. induction H.
  - exists []. reflexivity.
  - apply IHPartition.
  - apply IHPartition.
  - destruct IHPartition as [pre E]. exists (x :: pre). simpl. f_equal. assumption.
Qed.

Theorem partition_deterministic : forall {T} src src' hi lo,
  @Partition T src hi lo ->
  Partition src' hi lo ->
  src = src'.
Proof.
  intros. generalize dependent src'. induction H; intros; simpl in *.
  - invert H0. reflexivity.
  - invert H1.
    + apply IHPartition; assumption.
    + apply H4 in H as [].
    + apply H4 in H as [].
  - invert H2.
    + apply H in H6 as [].
    + apply IHPartition; assumption.
    + apply partition_src_app_lo in H9 as [pre E]. subst. rewrite in_app_iff in H7.
      apply Decidable.not_or in H7 as [H2 H3]. apply H3 in H0 as [].
  - invert H2.
    + apply H in H6 as [].
    + apply partition_src_app_lo in H1 as [pre E]. subst. rewrite in_app_iff in H0.
      apply Decidable.not_or in H0 as [H2 H3]. apply H3 in H7 as [].
    + f_equal. apply IHPartition; assumption.
Qed.

(* not efficient at all but not a problem right now *)
Fixpoint partition_src_with {T} (f : T -> T -> bool) hi lo :=
  match hi with
  | [] => lo
  | hd :: tl =>
      let recursed := partition_src_with f tl lo in
      (* NOTE: Checking for existence in `recursed` checks both `lo` AND `tl` at once. *)
      if existsb (f hd) recursed then recursed else hd :: recursed
  end.

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
  intros. generalize dependent x. generalize dependent f. generalize dependent lo.
  induction hi; intros; simpl in *. { destruct (count_acc 0 f x lo); reflexivity. }
  destruct (count_existsb f a (partition_src_with f hi lo) X); simpl in *.
  - destruct (X x a); [| apply IHhi; apply X]. rewrite count_S. subst. simpl in *.
    destruct (count_acc 0 f a (partition_src_with f hi lo)) eqn:Ep. { contradiction n. reflexivity. } clear n.
    rewrite IHhi in Ep; [| apply X]. destruct (count_acc 0 f a lo) eqn:El; [| symmetry; assumption].
    destruct (count_acc 0 f a hi). { discriminate Ep. } symmetry. assumption.
  - destruct (X x a); [| apply IHhi; apply X]. subst. repeat rewrite count_S.
    destruct (count_acc 0 f a (partition_src_with f hi lo)) eqn:Ep; [| contradiction n; intro C; discriminate C]. clear n.
    rewrite IHhi in Ep; [| apply X]. destruct (count_acc 0 f a lo); [| discriminate Ep]. reflexivity.
Qed.

Theorem existsb_partition_src : forall {T} x f hi lo,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  existsb (f x) (partition_src_with f hi lo) = orb (existsb (f x) hi) (existsb (f x) lo).
Proof.
  intros. destruct (count_existsb f x (partition_src_with f hi lo) X);
  destruct (count_existsb f x hi X); destruct (count_existsb f x lo X);
  try reflexivity; rewrite count_partition_src in n; destruct (count f x hi); auto; destruct (count f x lo); lia.
Qed.

Theorem in_partition_src : forall {T} x (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  In x (partition_src_with f hi lo) <-> (In x hi \/ In x lo).
Proof.
  intros. repeat (rewrite existsb_in_iff; [| apply X]).
  rewrite existsb_partition_src; [| apply X]. apply Bool.orb_true_iff.
Qed.

Theorem not_in_partition_src : forall {T} x (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  ~In x (partition_src_with f hi lo) <-> (~In x hi /\ ~In x lo).
Proof.
  intros. repeat (rewrite existsb_in_iff; [| apply X]).
  rewrite existsb_partition_src; [| apply X].
  repeat rewrite Bool.not_true_iff_false. apply Bool.orb_false_iff.
Qed.

Theorem partition_src_works : forall {T} (f : T -> T -> bool) hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  Partition (partition_src_with f hi lo) hi lo.
Proof.
  intros. generalize dependent f. generalize dependent lo. induction hi; intros; simpl in *. { constructor. }
  destruct (existsb_in f a (partition_src_with f hi lo) X).
  - rewrite in_partition_src in i; [| apply X]. destruct i.
    + apply PartitionCpHi; [| apply IHhi]; assumption.
    + destruct (existsb_in f a hi X).
      * apply PartitionCpHi; [| apply IHhi]; assumption.
      * apply PartitionCpLo; [| | apply IHhi]; assumption.
  - apply not_in_partition_src in n as [Hhi Hlo]; [| apply X]. apply PartitionMove; [assumption | | apply IHhi; assumption].
    intro C. apply in_partition_src in C as [C | C]; [| | assumption]. { apply Hhi in C as []. } apply Hlo in C as [].
Qed.

Theorem reflect_partition_src : forall {T} (f : T -> T -> bool) src hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  (partition_src_with f hi lo = src <-> Partition src hi lo).
Proof.
  split; intros.
  - subst. apply partition_src_works. assumption.
  - eapply partition_deterministic. { apply partition_src_works. assumption. } assumption.
Qed.

Definition ap_fst {A B C} : (A -> C) -> ((A * B) -> C) := fun f x => let (a, b) := x in f a.

Lemma existsb_map_fst : forall {A B} li f f' x y,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  existsb (f (x, y)) li = existsb (f' x) (map fst li).
Proof.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. rewrite H. destruct (f' x a). { reflexivity. } apply IHli. assumption.
Qed.

Lemma map_fst_partition_src : forall {A B} f f' hi lo,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  map fst (partition_src_with f hi lo) = partition_src_with f' (map fst hi) (map fst lo).
Proof.
  intros. generalize dependent lo. generalize dependent f'. generalize dependent f.
  induction hi; intros; simpl in *. { reflexivity. }
  destruct a. simpl. rewrite (existsb_map_fst _ f f' _ _ H). rewrite (IHhi _ _ H).
  destruct (existsb (f' a) (partition_src_with f' (map fst hi) (map fst lo))) eqn:E.
  - apply IHhi. assumption.
  - simpl. f_equal. apply IHhi. assumption.
Qed.

Theorem partition_map_fst : forall {A B} f f' hi lo,
  (forall a b : A, Bool.reflect (a = b) (f' a b)) ->
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  Partition (map fst (partition_src_with f hi lo)) (map fst hi) (map fst lo).
Proof.
  intros. erewrite map_fst_partition_src. { apply partition_src_works. apply X. } assumption.
Qed.

Definition fst_cmp {A B} := fun (a : string * A) (b : string * B) => eqb (fst a) (fst b).

Lemma has_cmp_fst : forall {T} li s t,
  existsb (@fst_cmp T T (s, t)) li = existsb (eqb s) (map fst li).
Proof.
  intros T li. induction li; intros; simpl in *. { reflexivity. }
  destruct a. unfold fst_cmp. simpl in *. destruct (eqb s s0). { reflexivity. }
  apply (IHli _ t).
Qed.

Fixpoint set_diff {T} (a b : list (string * T)) :=
  match a with
  | [] => []
  | hd :: tl =>
      let recursed := set_diff tl b in
      if (existsb (fst_cmp hd) tl || existsb (fst_cmp hd) b)%bool then recursed else hd :: recursed
  end.

Theorem incl_set_diff : forall {T} (a b : list (string * T)),
  incl (set_diff a b) a.
Proof.
  unfold incl. induction a; intros; simpl in *. { destruct H. }
  destruct (existsb (fst_cmp a) a0) eqn:Ea; simpl in *. { right. eapply IHa. apply H. }
  destruct (existsb (fst_cmp a) b) eqn:Eb; simpl in *. { right. eapply IHa. apply H. }
  destruct H. { left. assumption. } right. eapply IHa. apply H.
Qed.

Theorem partition_src_app : forall {T} (a b : list (string * T)),
  partition_src_with fst_cmp a b = set_diff a b ++ b.
Proof.
  induction a; intros; simpl in *. { reflexivity. }
  destruct a. repeat rewrite has_cmp_fst. erewrite map_fst_partition_src;
  [| intros; unfold fst_cmp; simpl; reflexivity]. rewrite (existsb_partition_src _ _ _ _ eqb_spec).
  destruct (existsb (eqb s) (map fst a0) || existsb (eqb s) (map fst b))%bool; simpl; f_equal; apply IHa.
Qed.
