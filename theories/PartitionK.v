(*
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
  Partition.

(* This whole file (as opposed to `Partition.v`)
 * stems from the subtle but crucial observation that
 * `In k (map fst li)` and `In (k, v) li` are not one-to-one. *)

Inductive PartitionK {K V} : list (K * V) -> list (K * V) -> list (K * V) -> Prop :=
  | PartitionKDone : forall lo,
      PartitionK [] [] lo
  | PartitionKCpLo : forall k v pf hi lo,
      FindKV k v lo ->
      PartitionK pf hi lo ->
      PartitionK pf ((k, v) :: hi) lo
  | PartitionKCpPf : forall k v pf hi lo,
      ~In k (map fst lo) ->
      FindKV k v pf ->
      FindKV k v hi -> (* <-- i.e., can't move b/c it's used again *)
      PartitionK pf hi lo ->
      PartitionK pf ((k, v) :: hi) lo
  | PartitionKMove : forall k v pf hi lo,
      ~In k (map fst lo) ->
      ~In k (map fst pf) -> (* <-- i.e. not a duplicate *)
      ~In k (map fst hi) -> (* <-- i.e. safe to move b/c not used again *)
      PartitionK pf hi lo ->
      PartitionK ((k, v) :: pf) ((k, v) :: hi) lo
  .
Arguments PartitionK {K V} pf hi lo.
Ltac partition_k_done := apply PartitionKDone.
Ltac partition_k_copy_lo := eapply PartitionKCpLo; [find_kv |].
Ltac partition_k_copy_pf := eapply PartitionKCpPf; [intros C; not_in C | find_kv | find_kv |].
Ltac partition_k_move := eapply PartitionKMove; [intros C; not_in C | intros C; not_in C | intros C; not_in C |].
Ltac partition_k_step := first [partition_k_done | partition_k_copy_lo | partition_k_copy_pf | partition_k_move].
Ltac try_partition_k := repeat partition_k_step.
Ltac partition_k := first [partition_k_done | first [partition_k_copy_lo | partition_k_copy_pf | partition_k_move]; partition_k].

Example partition_k_12345 :
  PartitionK
  [(4,4);(2,2)]
  [(1,1);(1,1);(1,1);(1,1);(1,1);(1,1);(4,4);(2,2);(3,3);(2,2);(2,2);(3,3)]
  [(1,1);(3,3);(5,5)].
Proof. partition_k. Qed.

Theorem partition_k_deterministic : forall {K V} pf pf' hi lo,
  @PartitionK K V pf hi lo ->
  PartitionK pf' hi lo ->
  pf = pf'.
Proof.
  intros. generalize dependent pf'. induction H; intros; simpl in *.
  - invert H0. reflexivity.
  - invert H1; try (apply IHPartitionK; assumption). apply find_kv_in_fst in H. apply H5 in H as [].
  - invert H3; try (apply IHPartitionK; assumption).
    assert (A := IHPartitionK _ H12). symmetry in A. subst.
    apply find_kv_in_fst in H0. apply H9 in H0 as [].
  - invert H3.
    + apply find_kv_in_fst in H9. apply H in H9 as [].
    + apply find_kv_in_fst in H11. apply H1 in H11 as [].
    + f_equal. apply IHPartitionK. assumption.
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
Fixpoint partition_k_pf_slow {K V} fk (hi lo : list (K * V)) : list (K * V) :=
  match hi with
  | [] => []
  | (k, v) :: tl =>
      let recursed := partition_k_pf_slow fk tl lo in
      match find_kv fk k lo with
      | Some vl => (* ==> there's a mapping for `k` in `lo` *)
          recursed
      | None => (* ==> `k` is never mapped in `lo` ==> either `PartitionKCpPf` or `PartitionKVMove` *)
          match find_kv fk k tl with
          | None => (* ==> ready for `PartitionKMove *)
              (k, v) :: recursed
          | Some vh => (* there's a mapping for `k` in `hi` ==> possibly `PartitionKCpPf` *)
              recursed
          end
      end
  end.

Fixpoint partition_k_pf_fast {K V} acc fk (hi lo : list (K * V)) : list (K * V) :=
  match hi with
  | [] => acc
  | (k, v) :: tl =>
      match find_kv fk k lo with
      | Some vl => partition_k_pf_fast acc fk tl lo
      | None =>
          match find_kv fk k tl with
          | Some vh => partition_k_pf_fast acc fk tl lo
          | None => partition_k_pf_fast ((k, v) :: acc) fk tl lo
          end
      end
  end.
Definition partition_k_pf {K V} fk (hi lo : list (K * V)) := rev' (partition_k_pf_fast [] fk hi lo).
Arguments partition_k_pf {K V}/ fk hi lo.

Lemma partition_k_pf_fast_app : forall {K V} hd tl fk hi lo,
  partition_k_pf_fast (hd ++ tl) fk hi lo = @partition_k_pf_fast K V hd fk hi lo ++ tl.
Proof.
  intros K V hd tl fk hi. generalize dependent hd. generalize dependent tl.
  generalize dependent fk. induction hi; intros; simpl in *. { reflexivity. }
  destruct a as [k v]. destruct (find_kv fk k lo) eqn:El. { apply IHhi. }
  destruct (find_kv fk k hi) eqn:Eh. { apply IHhi. }
  apply (IHhi _ _ ((k, v) :: hd)).
Qed.

Theorem partition_k_pf_fast_slow : forall {K V} fk hi lo,
  partition_k_pf fk hi lo = @partition_k_pf_slow K V fk hi lo.
Proof.
  intros K V fk hi. induction hi; intros; simpl in *. { reflexivity. }
  destruct a as [k v]. destruct (find_kv fk k lo) eqn:El. { apply IHhi. }
  destruct (find_kv fk k hi) eqn:Eh. { apply IHhi. }
  rewrite (partition_k_pf_fast_app [] [(k, v)]). rewrite <- IHhi.
  unfold rev'. rewrite <- rev_alt. rewrite rev_app_distr. repeat rewrite rev_alt. reflexivity.
Qed.

Theorem find_partition_k_pf : forall {K V} pf hi lo,
  @PartitionK K V pf hi lo ->
  forall k,
  (forall v, ~FindKV k v lo) ->
  forall v,
  FindKV k v hi ->
  FindKV k v pf.
Proof.
  intros K V pf hi lo Hp. induction Hp; intros; simpl in *.
  - assumption.
  - apply IHHp. { assumption. } invert H1. { apply H0 in H as []. } assumption.
  - apply IHHp. { assumption. } invert H3; assumption.
  - invert H3. { constructor. } constructor. { assumption. } apply IHHp; assumption.
Qed.

Theorem partition_k_pf_irrelevant : forall {K V} fk hi lo,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  forall k,
  @find_kv K V K fk k lo = None ->
  find_kv fk k hi = None ->
  find_kv fk k (partition_k_pf_slow fk hi lo) = None.
Proof.
  intros K V fk hi lo Xk k Hl Hh. generalize dependent fk. generalize dependent lo. generalize dependent k.
  induction hi; intros; simpl in *. { reflexivity. } destruct a as [ka va]. destruct (Xk k ka). { discriminate Hh. }
  destruct (find_kv fk ka lo) eqn:El. { apply IHhi; assumption. }
  destruct (find_kv fk ka hi) eqn:Eh. { apply IHhi; assumption. }
  simpl. destruct (Xk k ka); [contradiction n | clear n0]. apply IHhi; assumption.
Qed.

Theorem partition_k_fst_cmp : forall V hi lo pf,
  partition_pf fst_cmp hi lo = pf <-> @PartitionK _ V pf hi lo.
Proof.
  intros. rewrite partition_pf_fast_slow. split; intros.
  - subst. generalize dependent lo. induction hi; intros; simpl in *. { constructor. }
    destruct (existsb (fst_cmp a) lo) eqn:El; simpl in *. { destruct a. constructor. Search FindKV. Search find_kv. apply IHhi.
Qed.

Theorem partition_k_pf_works : forall {K V} fk (hi lo : list (K * V)) pf,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  partition_k_pf fk hi lo = pf <-> PartitionK pf hi lo.
Proof.
  intros K V fk hi lo pf Xk. rewrite partition_k_pf_fast_slow. split; intros.
  - subst. generalize dependent fk. generalize dependent lo. induction hi; intros; simpl in *. { constructor. }
    destruct a. destruct (find_kv fk k lo). { constructor.

  generalize dependent fk. generalize dependent fv. generalize dependent lo. generalize dependent pf.
  induction hi; intros; simpl in *. { invert Hp. constructor. } destruct a as [k v].
  destruct (partition_k_pf_slow fk fv hi lo) as [recursed |] eqn:Er; [| discriminate Hp].
  destruct (find_k fk k lo) eqn:El. {
    destruct (Xv v v0); invert Hp. apply PartitionKCpLo.
    - eapply reflect_find_k. { apply Xk. } assumption.
    - eapply IHhi. { apply Xv. } { apply Xk. } assumption. }
  destruct (find_k fk k hi) eqn:Eh.
  - destruct (Xv v v0); invert Hp. eapply PartitionKCpPf.
    + apply (not_in_fst_find _ _ _ Xk). apply (find_k_none _ _ _ Xk). assumption.
    + eapply find_partition_k_pf.
      * apply (IHhi _ _ _ Xv _ Xk Er).
      * apply (find_k_none _ _ _ Xk). assumption. 
      * apply (reflect_find_k _ _ _ _ Xk). assumption.
    + apply (reflect_find_k _ _ _ _ Xk). assumption.
    + apply (IHhi _ _ _ Xv _ Xk Er).
  - invert Hp. apply PartitionKMove; [| | | apply (IHhi _ _ _ Xv _ Xk Er)];
    eapply (not_in_fst_find _ _ _ Xk); apply (find_k_none _ _ _ Xk); try assumption.
    apply (partition_k_pf_irrelevant _ _ _ _ _ Xk Xv Er); assumption.
Qed.

Theorem reflect_partition_k_pf : forall {K V} fk fv hi lo pf,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  PartitionK pf hi lo <-> partition_k_pf fk fv hi lo = Some pf.
Proof.
  intros K V fk fv hi lo pf Xk Xv. split; intros; [| apply (partition_k_pf_works _ _ _ _ _ Xk Xv H)].
  rewrite partition_k_pf_fast_slow. induction H; intros; simpl in *; [reflexivity | | |]; rewrite IHPartitionK.
  - apply (reflect_find_k _ _ _ _ Xk) in H. rewrite H. destruct (Xv v v). { reflexivity. } contradiction n. reflexivity.
  - eapply (not_in_fst_find_none _ _ _ Xk) in H. rewrite H. apply (reflect_find_k _ _ _ _ Xk) in H1. rewrite H1.
    destruct (Xv v v). { reflexivity. } contradiction n. reflexivity.
  - eapply (not_in_fst_find_none _ _ _ Xk) in H. rewrite H.
    eapply (not_in_fst_find_none _ _ _ Xk) in H1. rewrite H1. reflexivity.
Qed.

Theorem reflect_not_partition_k_pf : forall {K V} fk fv hi lo,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_k_pf fk fv hi lo = None <-> forall pf, ~PartitionK pf hi lo.
Proof.
  intros K V fk fv hi lo Xk Xv. split; intros.
  - intro C. apply (reflect_partition_k_pf _ _ _ _ _ Xk Xv) in C. rewrite H in C. discriminate C.
  - destruct (partition_k_pf fk fv hi lo) eqn:Ep; [| reflexivity].
    apply (reflect_partition_k_pf _ _ _ _ _ Xk Xv) in Ep. apply H in Ep as [].
Qed.
*)
