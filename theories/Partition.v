From Coq Require Export
  Lia
  List
  String.
Export ListNotations.
From Lang Require Import
  Find
  FstCmp
  InTactics
  Invert
  PartitionKV
  StructuralFreeVariables.

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

Theorem slow_down : forall {T} f hi lo,
  rev' (@partition_pf_fast T [] f hi lo) = partition_pf_slow f hi lo.
Proof. intros. rewrite <- partition_pf_fast_slow. reflexivity. Qed.

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

Theorem slow_down_app : forall {T} f hi lo,
  @rev_append T (partition_pf_fast [] f hi lo) [] = partition_pf_slow f hi lo.
Proof. intros. rewrite <- slow_down. reflexivity. Qed.

Theorem slow_down_rev : forall {T} f hi lo,
  @rev T (partition_pf_fast [] f hi lo) = partition_pf_slow f hi lo.
Proof. intros. rewrite rev_alt. apply slow_down_app. Qed.

Theorem partition_without_kv : forall {V} fv hi lo pf,
  @partition_kv_pf _ V eqb fv hi lo = Some pf ->
  map fst (partition_pf fst_cmp hi lo) = map fst pf.
Proof.
  intros. rewrite partition_pf_fast_slow. rewrite partition_kv_pf_fast_slow in H.
  generalize dependent fv. generalize dependent lo. generalize dependent pf.
  induction hi; intros; simpl in *. { invert H. reflexivity. } destruct a as [s v].
  destruct (partition_kv_pf_slow eqb fv hi lo) eqn:Ep; [| discriminate H]. assert (Em := Ep). apply IHhi in Em.
  repeat rewrite has_cmp_fst. destruct (find_kv eqb s lo) eqn:El. {
    destruct (fv v v0) eqn:Ev; invert H. apply (reflect_find_kv _ _ _ _ eqb_spec) in El. apply find_kv_in_fst in El.
    apply (existsb_in_iff _ _ _ eqb_spec) in El. rewrite El. assumption. }
  destruct (find_kv eqb s hi) eqn:Eh. {
    destruct (fv v v0) eqn:Ev; invert H. apply (reflect_find_kv _ _ _ _ eqb_spec) in Eh. apply find_kv_in_fst in Eh.
    apply (existsb_in_iff _ _ _ eqb_spec) in Eh. rewrite Eh. rewrite Bool.orb_true_r. assumption. }
  invert H. destruct (existsb (eqb s) (map fst lo) || existsb (eqb s) (map fst hi))%bool eqn:E. 2: {
    simpl. f_equal. assumption. }
  apply Bool.orb_true_iff in E as [E | E]; apply (existsb_in_iff _ _ _ eqb_spec) in E;
  apply (in_fst_find_kv _ _ _ eqb_spec) in E as [found H]; apply (reflect_find_kv _ _ _ _ eqb_spec) in H;
  rewrite H in *; discriminate.
Qed.
