From Coq Require Export
  Lia
  List
  String.
Export ListNotations.
From Lang Require Import
  Count
  Find
  InTactics
  Invert
  Remove.

(* This whole file (as opposed to `Partition.v`)
 * stems from the subtle but crucial observation that
 * `In k (map fst li)` and `In (k, v) li` are not one-to-one. *)

(* TODO: Shadowing should be okay, so overhaul the whole semantics s.t. `src` is only the appended bit.
 * Then `~In k (map fst src)` just means "not *adding* two contradictory bindings" (right now, it's stronger).
 * WAIT, NEVER MIND: just use first instead of `In` *)
Inductive PartitionKV {K V} : list (K * V) -> list (K * V) -> list (K * V) -> Prop :=
  | PartitionKVDone : forall src,
      PartitionKV src [] src
  | PartitionKVCpHi : forall k v src hi lo,
      FindKV k v hi ->
      PartitionKV src hi lo ->
      PartitionKV src ((k, v) :: hi) lo
  | PartitionKVCpLo : forall k v src hi lo,
      ~In k (map fst hi) ->
      FindKV k v src -> (* `src`, not `lo`, since we can't allow different shadowed variables in `src` & `lo` *)
      PartitionKV src hi lo ->
      PartitionKV src ((k, v) :: hi) lo
  | PartitionKVMove : forall k v src hi lo,
      ~In k (map fst hi) ->
      ~In k (map fst src) ->
      PartitionKV src hi lo ->
      PartitionKV ((k, v) :: src) ((k, v) :: hi) lo
  .
Arguments PartitionKV {K V} src hi lo.
Ltac partition_kv_done := apply PartitionKVDone.
Ltac partition_kv_copy_hi := eapply PartitionKVCpHi; [find_kv |].
Ltac partition_kv_copy_lo := eapply PartitionKVCpLo; [intros C; not_in C | find_kv |].
Ltac partition_kv_move := eapply PartitionKVMove; [intros C; not_in C | intros C; not_in C |].
Ltac partition_kv_step := first [partition_kv_done | partition_kv_copy_hi | partition_kv_copy_lo | partition_kv_move].
Ltac try_partition_kv := repeat partition_kv_step.
Ltac partition_kv := first [partition_kv_done | first [partition_kv_copy_hi | partition_kv_copy_lo | partition_kv_move]; partition_kv].

Example partition_kv_12345 :
  PartitionKV
  [(4,4);(2,2);(1,1);(3,3);(5,5)]
  [(1,1);(1,1);(1,1);(1,1);(1,1);(1,1);(4,4);(2,2);(3,3);(2,2);(2,2);(3,3)]
  [(1,1);(3,3);(5,5)].
Proof. try_partition_kv. Qed.

(* This works but takes a ridiculously long time (~5 seconds).
Example not_partition_kv_12345 :
  ~PartitionKV
  [(4,4);(2,2);(1,1);(3,3);(5,5)] (* Here's the edit: v *)
  [(1,1);(1,1);(1,1);(1,1);(1,1);(1,1);(4,4);(2,2);(3,4);(2,2);(2,2);(3,3)]
  [(1,1);(3,3);(5,5)].
Proof.
  intros C. repeat (try clear f; try clear g;
    inversion C as [a b c d | a b c d e f Hp g h i | a b c d e f g Hp h i j | a b c d e f g Hp h i j];
    clear C; subst; simpl in *; try not_in f; try not_in g; try (contradiction e; auto_in); rename Hp into C).
Qed.
*)

Theorem partition_kv_src_app_lo : forall {K V} src hi lo,
  @PartitionKV K V src hi lo ->
  exists pre, src = pre ++ lo.
Proof.
  intros. induction H.
  - exists []. reflexivity.
  - apply IHPartitionKV.
  - apply IHPartitionKV.
  - destruct IHPartitionKV as [pre E]. exists ((k, v) :: pre). simpl. f_equal. assumption.
Qed.

Theorem partition_kv_deterministic : forall {K V} src src' hi lo,
  @PartitionKV K V src hi lo ->
  PartitionKV src' hi lo ->
  src = src'.
Proof.
  intros. generalize dependent src'. induction H; intros; simpl in *.
  - invert H0. reflexivity.
  - invert H1; try (apply IHPartitionKV; assumption). apply find_kv_in_fst in H. apply H6 in H as [].
  - invert H2; try (apply IHPartitionKV; assumption).
    assert (A := IHPartitionKV _ H10). symmetry in A. subst. clear H10 H7.
    apply partition_kv_src_app_lo in H1 as [pre E]. subst.
    rewrite in_map_fst_app in H9. apply Decidable.not_or in H9 as [H8 H9].
    apply find_kv_in_fst in H0. apply H9 in H0 as [].
  - invert H2.
    + apply find_kv_in_fst in H8. apply H in H8 as [].
    + apply partition_kv_src_app_lo in H1 as [pre E]. subst.
      rewrite in_map_fst_app in H0. apply Decidable.not_or in H0 as [H0 H1].
      apply find_kv_in_fst in H9. apply H1 in H9 as [].
    + f_equal. apply IHPartitionKV. assumption.
Qed.

Definition both_2 {K V} : (K -> K -> bool) -> (V -> V -> bool) -> (K * V) -> (K * V) -> bool := fun fk fv x1 x2 =>
  let (k1, v1) := x1 in let (k2, v2) := x2 in andb (fk k1 k2) (fv v1 v2).

Theorem both_2_reflect : forall {K V} fk fv,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  forall a b, Bool.reflect (a = b) (both_2 fk fv a b).
Proof.
  intros. destruct a as [k1 v1]. destruct b as [k2 v2]. simpl.
  destruct (X k1 k2); destruct (X0 v1 v2); subst; constructor;
  [reflexivity | | |]; intro C; invert C; contradiction.
Qed.

(* `fk` is equality on `K`
 * `fv` is equality on `V`
 * `hi` is the typing context
 * `lo` is the value context *)
Fixpoint partition_kv_src_with {K V} fk fv hi lo : option (list (K * V)) :=
  match hi with
  | [] => Some lo
  | (k, v) :: tl =>
      match partition_kv_src_with fk fv tl lo with
      | None => None
      | Some recursed =>
          (* NOTE: Checking for existence in `recursed` checks both `lo` AND `tl` at once. *)
          if existsb (both_2 fk fv (k, v)) recursed then Some recursed else
          if existsb (ap_fst_2 fk k) recursed then None else Some ((k, v) :: recursed)
      end
  end.

Theorem count_partition_kv_src : forall {K V} kv fk fv (hi lo : list (K * V)) src,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_src_with fk fv hi lo = Some src ->
  count (both_2 fk fv) kv src = (
    match count (both_2 fk fv) kv lo with
    | O =>
        match count (both_2 fk fv) kv hi with
        | O => O
        | S _ => 1
        end
    | S n =>
        S n
    end).
Proof.
  intros. generalize dependent kv. generalize dependent fk.
  generalize dependent fv. generalize dependent lo. generalize dependent src.
  induction hi; intros; simpl in *. { invert H. destruct (count_acc 0 (both_2 fk fv) kv src); reflexivity. }
  destruct kv as [k1 v1]. destruct a as [k2 v2]. simpl in *.
  destruct (partition_kv_src_with fk fv hi lo) eqn:Ep; [| discriminate H].
  destruct (count_existsb (both_2 fk fv) (k2, v2) l). { apply both_2_reflect; assumption. }
  - invert H. specialize (IHhi _ _ _ X0 _ X Ep). destruct (X k1 k2); destruct (X0 v1 v2);
    subst; simpl in *; repeat rewrite count_S; simpl in *.
    + specialize (IHhi (k2, v2)). destruct (count_acc 0 (both_2 fk fv) (k2, v2) src) eqn:E. { contradiction n; reflexivity. }
      clear n. destruct (count_acc 0 (both_2 fk fv) (k2, v2) lo) eqn:El; [| assumption].
      destruct (count_acc 0 (both_2 fk fv) (k2, v2) hi) eqn:Eh; [| assumption]. discriminate IHhi.
    + specialize (IHhi (k2, v1)). destruct (count_acc 0 (both_2 fk fv) (k2, v1) src) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k2, v1) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k2, v1) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
    + specialize (IHhi (k1, v2)). destruct (count_acc 0 (both_2 fk fv) (k1, v2) src) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k1, v2) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k1, v2) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
    + specialize (IHhi (k1, v1)). destruct (count_acc 0 (both_2 fk fv) (k1, v1) src) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k1, v1) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k1, v1) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
  - destruct (existsb (ap_fst_2 fk k2) l) eqn:Ee; invert H.
    destruct (count (both_2 fk fv) (k2, v2) l) eqn:Ec; [| contradiction n; intro C; discriminate C].
    clear n. simpl in *. specialize (IHhi _ _ _ X0 _ X Ep). destruct (X k1 k2); destruct (X0 v1 v2);
    subst; simpl in *; repeat rewrite count_S; simpl in *.
    + specialize (IHhi (k2, v2)). destruct (count_acc 0 (both_2 fk fv) (k2, v2) l) eqn:E; [| discriminate Ec].
      clear Ec. destruct (count_acc 0 (both_2 fk fv) (k2, v2) lo) eqn:El. { reflexivity. } discriminate IHhi.
    + specialize (IHhi (k2, v1)). destruct (count_acc 0 (both_2 fk fv) (k2, v1) l) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k2, v1) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k2, v1) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
    + specialize (IHhi (k1, v2)). destruct (count_acc 0 (both_2 fk fv) (k1, v2) l) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k1, v2) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k1, v2) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
    + specialize (IHhi (k1, v1)). destruct (count_acc 0 (both_2 fk fv) (k1, v1) l) eqn:E;
      destruct (count_acc 0 (both_2 fk fv) (k1, v1) lo) eqn:El; [| discriminate IHhi | | assumption];
      destruct (count_acc 0 (both_2 fk fv) (k1, v1) hi) eqn:Eh; try discriminate IHhi; [reflexivity | assumption].
Qed.

Theorem existsb_partition_kv_src : forall {K V} kv fk fv (hi lo : list (K * V)) src,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_src_with fk fv hi lo = Some src ->
  existsb (both_2 fk fv kv) src = orb (existsb (both_2 fk fv kv) hi) (existsb (both_2 fk fv kv) lo).
Proof.
  intros. assert (A := both_2_reflect _ _ X X0).
  destruct (existsb (both_2 fk fv kv) src) eqn:Es;
  destruct (existsb (both_2 fk fv kv) hi) eqn:Eh;
  destruct (existsb (both_2 fk fv kv) lo) eqn:El;
  try reflexivity; simpl in *;
  try (apply count_existsb_true in Es; [| assumption]); try (apply count_existsb_false in Es; [| assumption]);
  try (apply count_existsb_true in Eh; [| assumption]); try (apply count_existsb_false in Eh; [| assumption]);
  try (apply count_existsb_true in El; [| assumption]); try (apply count_existsb_false in El; [| assumption]);
  rewrite (count_partition_kv_src _ _ _ hi lo) in Es; try assumption;
  destruct (count (both_2 fk fv) kv hi) eqn:Ech; try (contradiction Eh; reflexivity); try discriminate Eh;
  destruct (count (both_2 fk fv) kv lo) eqn:Ecl; try (contradiction Es; reflexivity); discriminate Es.
Qed.

Theorem in_partition_kv_src : forall {K V} k fk fv (hi lo : list (K * V)) src,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_src_with fk fv hi lo = Some src ->
  In k src <-> (In k hi \/ In k lo).
Proof.
  intros. assert (A := both_2_reflect _ _ X X0). repeat (rewrite existsb_in_iff; [| apply A]).
  erewrite existsb_partition_kv_src; [| assumption | assumption | apply H]. apply Bool.orb_true_iff.
Qed.

Theorem not_in_partition_kv_src : forall {K V} kv fk fv (hi lo : list (K * V)) src,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_src_with fk fv hi lo = Some src ->
  ~In kv src <-> (~In kv hi /\ ~In kv lo).
Proof.
  intros. assert (A := both_2_reflect _ _ X X0). repeat (rewrite existsb_in_iff; [| apply A]).
  erewrite existsb_partition_kv_src; [| assumption | assumption | apply H].
  repeat rewrite Bool.not_true_iff_false. apply Bool.orb_false_iff.
Qed.

Theorem partition_kv_src_works : forall {K V} fk fv (hi lo : list (K * V)) src,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_src_with fk fv hi lo = Some src ->
  PartitionKV src hi lo.
Proof.
  intros. generalize dependent fk. generalize dependent fv. generalize dependent lo. generalize dependent src.
  induction hi; intros; simpl in *. { invert H. constructor. } assert (A := both_2_reflect _ _ X X0).
  destruct a. destruct (partition_kv_src_with fk fv hi lo) as [p |] eqn:Ep; [| discriminate H].
  erewrite existsb_partition_kv_src in H; [| assumption | assumption | apply Ep].
  destruct (existsb (both_2 fk fv (k, v)) hi) eqn:Eh; simpl in *.
  - invert H. apply existsb_in_iff in Eh; [| assumption]. apply PartitionKVCpHi. { assumption. }
    eapply IHhi. { apply X0. } { apply X. } assumption.
  - apply existsb_in_iff_not in Eh; [| assumption]. destruct (existsb_in _ k (map fst hi) X).
    + admit. (* <-- This is the problem! *)
    + apply PartitionKVCpLo.
    apply PartitionKVCpLo. destruct (existsb (both_2 fk fv (k, v)) lo) eqn:El; simpl in *.
    + invert H. 

  destruct (existsb (both_2 fk fv (k, v)) p) eqn:Ee.
  - invert H. erewrite existsb_partition_kv_src in Ee; [| assumption | assumption | apply Ep].
    apply Bool.orb_prop in Ee as [Ee | Ee]; (apply existsb_in_iff in Ee; [| assumption]).
    + apply PartitionKVCpHi. { assumption. } eapply IHhi. { apply X0. } { apply X. } assumption.
    + 
    apply existsb_in_iff in Ee; [| assumption]. apply PartitionKVCpHi. { assumption. } erewrite count_partition_kv_src in n; [| assumption | assumption | apply Ep].
    destruct (count (both_2 fk fv) (k, v) lo) eqn:El.
    + destruct (count (both_2 fk fv) (k, v) hi) eqn:Eh. { contradiction n. reflexivity. } clear n.
      apply PartitionKVCpHi. { Search count. apply count_in.
    destruct (count_existsb _ (k, v) lo A) eqn:El.
    apply PartitionKVCpHi.
    + apply count_partition

  destruct a. destruct (existsb (ap_fst_2 f k) (partition_kv_src_with f hi lo)) eqn:E.
  - rewrite existsb_partition_kv_src in E; [| assumption]. apply Bool.orb_prop in E as [E | E].
    + apply PartitionKVCpHi; [| apply IHhi]. ; assumption.
    + destruct (existsb_in f a hi X).
      * apply PartitionCpHi; [| apply IHhi]; assumption.
      * apply PartitionCpLo; [| | apply IHhi]; assumption.
  - apply not_in_partition_kv_src in n as [Hhi Hlo]; [| apply X]. apply PartitionMove; [assumption | | apply IHhi; assumption].
    intro C. apply in_partition_kv_src in C as [C | C]; [| | assumption]. { apply Hhi in C as []. } apply Hlo in C as [].
Qed.

Theorem reflect_partition_kv_src : forall {T} (f : T -> T -> bool) src hi lo,
  (forall a b, Bool.reflect (a = b) (f a b)) ->
  (partition_kv_src_with f hi lo = src <-> Partition src hi lo).
Proof.
  split; intros.
  - subst. apply partition_kv_src_works. assumption.
  - eapply partition_kv_deterministic. { apply partition_kv_src_works. assumption. } assumption.
Qed.

Definition ap_fst {A B C} : (A -> C) -> ((A * B) -> C) := fun f x => let (a, b) := x in f a.

Lemma existsb_map_fst : forall {A B} li f f' x y,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  existsb (f (x, y)) li = existsb (f' x) (map fst li).
Proof.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. rewrite H. destruct (f' x a). { reflexivity. } apply IHli. assumption.
Qed.

Lemma map_fst_partition_kv_src : forall {A B} f f' hi lo,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  map fst (partition_kv_src_with f hi lo) = partition_kv_src_with f' (map fst hi) (map fst lo).
Proof.
  intros. generalize dependent lo. generalize dependent f'. generalize dependent f.
  induction hi; intros; simpl in *. { reflexivity. }
  destruct a. simpl. rewrite (existsb_map_fst _ f f' _ _ H). rewrite (IHhi _ _ H).
  destruct (existsb (f' a) (partition_kv_src_with f' (map fst hi) (map fst lo))) eqn:E.
  - apply IHhi. assumption.
  - simpl. f_equal. apply IHhi. assumption.
Qed.

Theorem partition_kv_map_fst : forall {A B} f f' hi lo,
  (forall a b : A, Bool.reflect (a = b) (f' a b)) ->
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  Partition (map fst (partition_kv_src_with f hi lo)) (map fst hi) (map fst lo).
Proof.
  intros. erewrite map_fst_partition_kv_src. { apply partition_kv_src_works. apply X. } assumption.
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

Theorem partition_kv_src_app : forall {T} (a b : list (string * T)),
  partition_kv_src_with fst_cmp a b = set_diff a b ++ b.
Proof.
  induction a; intros; simpl in *. { reflexivity. }
  destruct a. repeat rewrite has_cmp_fst. erewrite map_fst_partition_kv_src;
  [| intros; unfold fst_cmp; simpl; reflexivity]. rewrite (existsb_partition_kv_src _ _ _ _ eqb_spec).
  destruct (existsb (eqb s) (map fst a0) || existsb (eqb s) (map fst b))%bool; simpl; f_equal; apply IHa.
Qed.
