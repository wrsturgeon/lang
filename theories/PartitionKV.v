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

Inductive PartitionKV {K V} : list (K * V) -> list (K * V) -> list (K * V) -> Prop :=
  | PartitionKVDone : forall lo,
      PartitionKV [] [] lo
  | PartitionKVCpLo : forall k v pf hi lo,
      FindKV k v lo ->
      PartitionKV pf hi lo ->
      PartitionKV pf ((k, v) :: hi) lo
  | PartitionKVCpPf : forall k v pf hi lo,
      ~In k (map fst lo) ->
      FindKV k v pf ->
      FindKV k v hi -> (* <-- i.e., can't move b/c it's used again *)
      PartitionKV pf hi lo ->
      PartitionKV pf ((k, v) :: hi) lo
  | PartitionKVMove : forall k v pf hi lo,
      ~In k (map fst lo) ->
      ~In k (map fst pf) -> (* <-- i.e. not a duplicate *)
      ~In k (map fst hi) -> (* <-- i.e. safe to move b/c not used again *)
      PartitionKV pf hi lo ->
      PartitionKV ((k, v) :: pf) ((k, v) :: hi) lo
  .
Arguments PartitionKV {K V} pf hi lo.
Ltac partition_kv_done := apply PartitionKVDone.
Ltac partition_kv_copy_lo := eapply PartitionKVCpLo; [find_kv |].
Ltac partition_kv_copy_pf := eapply PartitionKVCpPf; [intros C; not_in C | find_kv | find_kv |].
Ltac partition_kv_move := eapply PartitionKVMove; [intros C; not_in C | intros C; not_in C | intros C; not_in C |].
Ltac partition_kv_step := first [partition_kv_done | partition_kv_copy_lo | partition_kv_copy_pf | partition_kv_move].
Ltac try_partition_kv := repeat partition_kv_step.
Ltac partition_kv := first [partition_kv_done | first [partition_kv_copy_lo | partition_kv_copy_pf | partition_kv_move]; partition_kv].

Example partition_kv_12345 :
  PartitionKV
  [(4,4);(2,2)]
  [(1,1);(1,1);(1,1);(1,1);(1,1);(1,1);(4,4);(2,2);(3,3);(2,2);(2,2);(3,3)]
  [(1,1);(3,3);(5,5)].
Proof. partition_kv. Qed.

Theorem partition_kv_deterministic : forall {K V} pf pf' hi lo,
  @PartitionKV K V pf hi lo ->
  PartitionKV pf' hi lo ->
  pf = pf'.
Proof.
  intros. generalize dependent pf'. induction H; intros; simpl in *.
  - invert H0. reflexivity.
  - invert H1; try (apply IHPartitionKV; assumption). apply find_kv_in_fst in H. apply H5 in H as [].
  - invert H3; try (apply IHPartitionKV; assumption).
    assert (A := IHPartitionKV _ H12). symmetry in A. subst.
    apply find_kv_in_fst in H0. apply H9 in H0 as [].
  - invert H3.
    + apply find_kv_in_fst in H9. apply H in H9 as [].
    + apply find_kv_in_fst in H11. apply H1 in H11 as [].
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
Fixpoint partition_kv_pf_slow {K V} fk (fv : V -> V -> bool) hi lo : option (list (K * V)) :=
  match hi with
  | [] => Some []
  | (k, v) :: tl =>
      match partition_kv_pf_slow fk fv tl lo with
      | None => None
      | Some recursed =>
          match find_kv fk k lo with
          | Some vl => (* ==> there's a mapping for `k` in `lo` *)
              if fv v vl then
                (* ==> ready for `PartitionKVCpLo` *)
                Some recursed
              else
                (* ==> inconsistent mappings *)
                None
          | None => (* ==> `k` is never mapped in `lo` ==> either `PartitionKVCpPf` or `PartitionKVMove` *)
              match find_kv fk k tl with
              | None => (* ==> ready for `PartitionKVMove *)
                  Some ((k, v) :: recursed)
              | Some vh => (* there's a mapping for `k` in `hi` ==> possibly `PartitionKVCpPf` *)
                  if fv v vh then
                    (* okay, right mapping at least: looking promising.
                     * the only remaining condition for `PartitionKVCpPf` is `FindKV k v pf`.
                     * recall that `pf` is the output of this function.
                     * so can we prove that, by making it here, it already must be the case?
                     * TODO *)
                    Some recursed
                  else
                    (* ==> inconsistent mappings *)
                    None
              end
          end
      end
  end.

Fixpoint partition_kv_pf_fast {K V} acc fk (fv : V -> V -> bool) hi lo : option (list (K * V)) :=
  match hi with
  | [] => Some acc
  | (k, v) :: tl =>
      match find_kv fk k lo with
      | Some vl => if fv v vl then partition_kv_pf_fast acc fk fv tl lo else None
      | None =>
          match find_kv fk k tl with
          | Some vh => if fv v vh then partition_kv_pf_fast acc fk fv tl lo else None
          | None => partition_kv_pf_fast ((k, v) :: acc) fk fv tl lo
          end
      end
  end.
Definition partition_kv_pf {K V} fk fv (hi lo : list (K * V)) :=
  match partition_kv_pf_fast [] fk fv hi lo with
  | None => None
  | Some li => Some (rev' li)
  end.
Arguments partition_kv_pf {K V}/ fk fv hi lo.

Lemma partition_kv_pf_fast_app : forall {K V} hd tl fk fv hi lo,
  partition_kv_pf_fast (hd ++ tl) fk fv hi lo = option_map (fun li => li ++ tl) (@partition_kv_pf_fast K V hd fk fv hi lo).
Proof.
  intros K V hd tl fk fv hi. generalize dependent hd. generalize dependent tl.
  generalize dependent fk. generalize dependent fv. induction hi; intros; simpl in *. { reflexivity. }
  destruct a as [k v]. destruct (find_kv fk k lo) eqn:El.
  - destruct (fv v v0). { apply IHhi. } reflexivity.
  - destruct (find_kv fk k hi) eqn:Eh.
    + destruct (fv v v0); [| reflexivity]. apply IHhi.
    + apply (IHhi _ _ _ ((k, v) :: hd)).
Qed.

Theorem partition_kv_pf_fast_slow : forall {K V} fk fv hi lo,
  partition_kv_pf fk fv hi lo = @partition_kv_pf_slow K V fk fv hi lo.
Proof.
  intros K V fk fv hi. induction hi; intros; simpl in *. { reflexivity. }
  destruct a as [k v]. destruct (find_kv fk k lo) eqn:El.
  - destruct (fv v v0); [rewrite IHhi |]; destruct (partition_kv_pf_slow fk fv hi lo); reflexivity.
  - destruct (find_kv fk k hi) eqn:Eh.
    + destruct (fv v v0); [rewrite IHhi |]; destruct (partition_kv_pf_slow fk fv hi lo); reflexivity.
    + rewrite (partition_kv_pf_fast_app [] [(k, v)]). rewrite <- IHhi.
      destruct (partition_kv_pf_fast [] fk fv hi lo); [| reflexivity].
      simpl in *. unfold rev'. repeat rewrite <- rev_alt. rewrite rev_app_distr. reflexivity.
Qed.

Theorem find_partition_kv_pf : forall {K V} pf hi lo,
  @PartitionKV K V pf hi lo ->
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

Theorem partition_kv_pf_irrelevant : forall {K V} fk fv hi lo pf,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_pf_slow fk fv hi lo = Some pf ->
  forall k,
  find_kv fk k lo = None ->
  find_kv fk k hi = None ->
  find_kv fk k pf = None.
Proof.
  intros K V fk fv hi lo pf Xk Xv Hp k Hl Hh. generalize dependent fk. generalize dependent fv. generalize dependent lo.
  generalize dependent pf. generalize dependent k. induction hi; intros; simpl in *. { invert Hp. reflexivity. }
  destruct a as [ka va]. destruct (Xk k ka). { discriminate Hh. }
  destruct (partition_kv_pf_slow fk fv hi lo) as [recursed |] eqn:Er; [| discriminate Hp].
  destruct (find_kv fk ka lo) eqn:El.
  - destruct (Xv va v); invert Hp. apply (IHhi _ _ _ _ Xv _ Xk Er); assumption.
  - destruct (find_kv fk ka hi) eqn:Eh.
    + destruct (Xv va v); invert Hp. apply (IHhi _ _ _ _ Xv _ Xk Er); assumption.
    + invert Hp. simpl. destruct (Xk k ka). { contradiction n. } clear n0.
      apply (IHhi _ _ _ _ Xv _ Xk Er); assumption.
Qed.

Theorem partition_kv_pf_works : forall {K V} fk fv (hi lo : list (K * V)) pf,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_pf fk fv hi lo = Some pf ->
  PartitionKV pf hi lo.
Proof.
  intros K V fk fv hi lo pf Xk Xv Hp. rewrite partition_kv_pf_fast_slow in Hp.
  generalize dependent fk. generalize dependent fv. generalize dependent lo. generalize dependent pf.
  induction hi; intros; simpl in *. { invert Hp. constructor. } destruct a as [k v].
  destruct (partition_kv_pf_slow fk fv hi lo) as [recursed |] eqn:Er; [| discriminate Hp].
  destruct (find_kv fk k lo) eqn:El. {
    destruct (Xv v v0); invert Hp. apply PartitionKVCpLo.
    - eapply reflect_find_kv. { apply Xk. } assumption.
    - eapply IHhi. { apply Xv. } { apply Xk. } assumption. }
  destruct (find_kv fk k hi) eqn:Eh.
  - destruct (Xv v v0); invert Hp. eapply PartitionKVCpPf.
    + apply (not_in_fst_find _ _ _ Xk). apply (find_kv_none _ _ _ Xk). assumption.
    + eapply find_partition_kv_pf.
      * apply (IHhi _ _ _ Xv _ Xk Er).
      * apply (find_kv_none _ _ _ Xk). assumption. 
      * apply (reflect_find_kv _ _ _ _ Xk). assumption.
    + apply (reflect_find_kv _ _ _ _ Xk). assumption.
    + apply (IHhi _ _ _ Xv _ Xk Er).
  - invert Hp. apply PartitionKVMove; [| | | apply (IHhi _ _ _ Xv _ Xk Er)];
    eapply (not_in_fst_find _ _ _ Xk); apply (find_kv_none _ _ _ Xk); try assumption.
    apply (partition_kv_pf_irrelevant _ _ _ _ _ Xk Xv Er); assumption.
Qed.

Theorem reflect_partition_kv_pf : forall {K V} fk fv hi lo pf,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  PartitionKV pf hi lo <-> partition_kv_pf fk fv hi lo = Some pf.
Proof.
  intros K V fk fv hi lo pf Xk Xv. split; intros; [| apply (partition_kv_pf_works _ _ _ _ _ Xk Xv H)].
  rewrite partition_kv_pf_fast_slow. induction H; intros; simpl in *; [reflexivity | | |]; rewrite IHPartitionKV.
  - apply (reflect_find_kv _ _ _ _ Xk) in H. rewrite H. destruct (Xv v v). { reflexivity. } contradiction n. reflexivity.
  - eapply (not_in_fst_find_none _ _ _ Xk) in H. rewrite H. apply (reflect_find_kv _ _ _ _ Xk) in H1. rewrite H1.
    destruct (Xv v v). { reflexivity. } contradiction n. reflexivity.
  - eapply (not_in_fst_find_none _ _ _ Xk) in H. rewrite H.
    eapply (not_in_fst_find_none _ _ _ Xk) in H1. rewrite H1. reflexivity.
Qed.

Theorem reflect_not_partition_kv_pf : forall {K V} fk fv hi lo,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (forall a b : V, Bool.reflect (a = b) (fv a b)) ->
  partition_kv_pf fk fv hi lo = None <-> forall pf, ~PartitionKV pf hi lo.
Proof.
  intros K V fk fv hi lo Xk Xv. split; intros.
  - intro C. apply (reflect_partition_kv_pf _ _ _ _ _ Xk Xv) in C. rewrite H in C. discriminate C.
  - destruct (partition_kv_pf fk fv hi lo) eqn:Ep; [| reflexivity].
    apply (reflect_partition_kv_pf _ _ _ _ _ Xk Xv) in Ep. apply H in Ep as [].
Qed.
