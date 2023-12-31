From Coq Require Export
  Lia
  List
  String.
Export ListNotations.
From Lang Require Import
  FstCmp
  InTactics
  Invert.

(* Partition a context into types (which allow structural rules) and values (which don't). *)
Inductive Partition {T} : list T -> list T -> list T -> Prop :=
  | PartitionDone : forall lo,
      Partition [] [] lo
  | PartitionCpLo : forall x pf hi lo,
      In x lo ->
      Partition pf hi lo ->
      Partition pf (x :: hi) lo
  | PartitionCpPf : forall x pf hi lo,
      ~In x lo ->
      In x pf ->
      In x hi ->
      Partition pf hi lo ->
      Partition pf (x :: hi) lo
  | PartitionMove : forall x pf hi lo,
      ~In x lo ->
      ~In x pf ->
      ~In x hi ->
      Partition pf hi lo ->
      Partition (x :: pf) (x :: hi) lo
  .
Arguments Partition {T} pf hi lo.
Ltac partition_done := apply PartitionDone.
Ltac partition_copy_lo := eapply PartitionCpLo; [auto_in |].
Ltac partition_copy_pf := eapply PartitionCpPf; [intros C; not_in C | auto_in | auto_in |].
Ltac partition_move := eapply PartitionMove; [intros C; not_in C | intros C; not_in C | intros C; not_in C |].
Ltac partition_step := first [partition_done | partition_copy_lo | partition_copy_pf | partition_move].
Ltac try_partition := repeat partition_step.
Ltac partition := first [partition_done | first [partition_copy_lo | partition_copy_pf | partition_move]; partition].

Example partition_12345 : Partition [4;2] [1;1;1;1;1;1;4;2;3;2;2;3] [1;3;5]. Proof. partition. Qed.

Theorem partition_deterministic : forall {T} pf pf' hi lo,
  @Partition T pf hi lo ->
  Partition pf' hi lo ->
  pf = pf'.
Proof.
  intros. generalize dependent pf'. induction H; intros; simpl in *.
  - invert H0. reflexivity.
  - invert H1.
    + apply IHPartition; assumption.
    + apply H4 in H as [].
    + apply H4 in H as [].
  - invert H3.
    + apply H in H7 as [].
    + apply IHPartition. assumption.
    + apply H9 in H1 as [].
  - invert H3.
    + apply H in H7 as [].
    + apply H1 in H9 as [].
    + f_equal. apply IHPartition. assumption.
Qed.

Fixpoint partition_pf_slow {T} f (hi lo : list T) :=
  match hi with
  | [] => []
  | hd :: tl =>
      let recursed := partition_pf_slow f tl lo in
      if (existsb (f hd) lo || existsb (f hd) tl)%bool then recursed else hd :: recursed
  end.

Fixpoint partition_pf_fast {T} acc f (hi lo : list T) :=
  match hi with
  | [] => acc
  | hd :: tl =>
      partition_pf_fast (if (existsb (f hd) lo || existsb (f hd) tl)%bool then acc else hd :: acc) f tl lo
  end.
Definition partition_pf {T} f hi lo := rev' (@partition_pf_fast T [] f hi lo).
Arguments partition_pf {T}/ f hi lo.

Theorem partition_pf_fast_acc : forall {T} hd tl f hi lo,
  @partition_pf_fast T (hd ++ tl) f hi lo = partition_pf_fast hd f hi lo ++ tl.
Proof.
  intros T hd tl f hi. generalize dependent hd. generalize dependent tl. generalize dependent f.
  induction hi; intros; simpl in *. { reflexivity. }
  destruct (existsb (f a) lo); simpl in *. { apply IHhi. }
  destruct (existsb (f a) hi); simpl in *. { apply IHhi. }
  apply (IHhi _ tl (a :: hd)).
Qed.

Theorem partition_pf_fast_slow : forall {T} f hi lo,
  @partition_pf T f hi lo = partition_pf_slow f hi lo.
Proof.
  intros T f hi. generalize dependent f. induction hi; intros; simpl in *. { reflexivity. }
  destruct (existsb (f a) lo); simpl in *. { apply IHhi. }
  destruct (existsb (f a) hi); simpl in *. { apply IHhi. }
  rewrite (partition_pf_fast_acc [] [a]). unfold rev'. rewrite <- rev_alt. rewrite rev_app_distr. simpl.
  f_equal. rewrite rev_alt. apply IHhi.
Qed.

Theorem in_partition_pf : forall {T} x f hi lo,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  In x (partition_pf f hi lo) <-> (In x hi /\ ~In x lo).
Proof.
  split; intros; rewrite partition_pf_fast_slow in *.
  - generalize dependent x. generalize dependent f. generalize dependent lo.
    induction hi; intros; simpl in *. { destruct H. }
    destruct (existsb_in f a lo X). { apply (IHhi _ _ X) in H as [Hh Hl]. split; [right |]; assumption. }
    destruct (existsb_in f a hi X). { apply (IHhi _ _ X) in H as [Hh Hl]. split; [right |]; assumption. }
    destruct H. { subst. split. { left. reflexivity. } assumption. }
    apply (IHhi _ _ X) in H as [Hh Hl]. split; [right |]; assumption.
  - destruct H as [Hh Hl]. generalize dependent x. generalize dependent f. generalize dependent lo.
    induction hi; intros; simpl in *; destruct Hh; [symmetry in H; subst |];
    (destruct (existsb_in f a lo X); [apply (IHhi _ _ X); auto; apply Hl in i as [] |]);
    (destruct (existsb_in f a hi X); [apply (IHhi _ _ X); assumption |]). { left. reflexivity. }
    simpl. destruct (X a x). { left. assumption. } right. apply (IHhi _ _ X); assumption.
Qed.

Lemma incl_partition_pf : forall {T} f hi lo,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  incl (partition_pf f hi lo) hi.
Proof. unfold incl. intros. apply (in_partition_pf _ _ _ _ X) in H as [Hh Hl]. assumption. Qed.

Theorem partition_pf_works : forall {T} f hi lo,
  (forall a b : T, Bool.reflect (a = b) (f a b)) ->
  Partition (partition_pf f hi lo) hi lo.
Proof.
  intros. rewrite partition_pf_fast_slow. generalize dependent f. generalize dependent lo.
  induction hi; intros; simpl in *. { constructor. }
  destruct (existsb_in f a lo X). { apply PartitionCpLo; [assumption | apply (IHhi _ _ X)]. }
  destruct (existsb_in f a hi X). {
    apply PartitionCpPf; [assumption | | assumption | apply (IHhi _ _ X)].
    rewrite <- partition_pf_fast_slow. apply (in_partition_pf _ _ _ _ X). split; assumption. }
  apply PartitionMove; [assumption | | assumption | apply (IHhi _ _ X)].
  intro C. rewrite <- partition_pf_fast_slow in C.
  apply (in_partition_pf _ _ _ _ X) in C as [Hh Hl]. apply n0 in Hh as [].
Qed.

Theorem reflect_partition_pf : forall {T} (f : T -> T -> bool) pf hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  (partition_pf f hi lo = pf <-> Partition pf hi lo).
Proof.
  split; intros.
  - subst. apply partition_pf_works. assumption.
  - eapply partition_deterministic. { apply partition_pf_works. assumption. } assumption.
Qed.

Lemma map_fst_partition_pf : forall {A B} f f' hi lo,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  map fst (partition_pf f hi lo) = partition_pf f' (map fst hi) (map fst lo).
Proof.
  intros. repeat rewrite partition_pf_fast_slow. generalize dependent lo. generalize dependent f'. generalize dependent f.
  induction hi; intros; simpl in *. { reflexivity. }
  destruct a as [a b]. simpl in *. repeat rewrite (existsb_map_fst _ f f' _ _ H).
  destruct (existsb (f' a) (map fst lo)). { apply (IHhi _ _ H). }
  destruct (existsb (f' a) (map fst hi)). { apply (IHhi _ _ H). }
  simpl. f_equal. apply (IHhi _ _ H).
Qed.

Theorem partition_map_fst : forall {A B} f f' hi lo,
  (forall a b : A, Bool.reflect (a = b) (f' a b)) ->
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  Partition (map fst (partition_pf f hi lo)) (map fst hi) (map fst lo).
Proof.
  intros. erewrite map_fst_partition_pf. { apply partition_pf_works. apply X. } assumption.
Qed.
