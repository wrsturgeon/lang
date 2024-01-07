From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  Invert.

Inductive FindKV {K V} (k : K) (v : V) : list (K * V) -> Prop :=
  | FindKVHd : forall tl,
      FindKV k v ((k, v) :: tl)
  | FindKVTl : forall hk hv tl,
      k <> hk -> (* <-- the crucial bit *)
      FindKV k v tl ->
      FindKV k v ((hk, hv) :: tl)
  .
Ltac find_kv_hd := apply FindKVHd.
Ltac find_kv_tl := apply FindKVTl; [intros C; discriminate C |].
Ltac find_kv := first [find_kv_hd | find_kv_tl; find_kv].

Example find_kv_12345 : FindKV 3 3 [(1,1);(2,2);(3,3);(4,4);(5,5)]. Proof. find_kv. Qed.

(* And here's the crucial difference with `In` *)
Example find_kv_12345_shadow : ~FindKV 3 9 [(1,1);(2,2);(3,3);(3,9);(4,4);(5,5)].
Proof.
  intro C. repeat (
    inversion C as [| m n tl Hne H Em]; subst; clear C; rename H into C;
    try (contradiction Hne; reflexivity); clear Hne).
Qed.

Theorem find_kv_in_fst : forall {K V} k v li,
  @FindKV K V k v li ->
  In k (map fst li).
Proof.
  intros. induction H.
  - left. reflexivity.
  - right. assumption.
Qed.

Theorem not_in_fst_find : forall {K V} fk k li,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (~In k (map fst li)) <-> forall v, ~@FindKV K V k v li.
Proof.
  split.
  - generalize dependent k. induction li; intros; intro C; simpl in *. { invert C. }
    destruct a as [ka va]. simpl in *. apply Decidable.not_or in H as [Hk Hi]. invert C. { contradiction Hk. reflexivity. }
    eapply IHli. { apply Hi. } apply H3.
  - generalize dependent k. induction li; intros; intros []; destruct a as [ka va]; simpl in *; subst.
    + apply (H va). constructor.
    + destruct (X k ka). { subst. apply (H va). constructor. }
      assert (A : forall v, ~FindKV k v li). { intros v C. eapply H. constructor. { assumption. } apply C. }
      eapply IHli. { apply A. } assumption.
Qed.

Theorem in_fst_find_kv : forall {K V} f k li,
  (forall a b : K, Bool.reflect (a = b) (f a b)) ->
  In k (map fst li) ->
  exists v, @FindKV K V k v li.
Proof.
  intros. generalize dependent k. induction li; intros; destruct H; destruct a as [ka va]; simpl in *; subst.
  - exists va. constructor.
  - destruct (X k ka). { exists va. subst. constructor. }
    apply IHli in H as [v IH]. exists v. constructor; assumption.
Qed.

Theorem find_kv_deterministic : forall {K V} k v v' li,
  @FindKV K V k v li ->
  FindKV k v' li ->
  v = v'.
Proof.
  intros. generalize dependent v'. induction H; intros; simpl in *.
  - invert H0. { reflexivity. } contradiction H2. reflexivity.
  - invert H1. { contradiction H. reflexivity. } apply IHFindKV. assumption.
Qed.

Fixpoint find_kv {K V C} (fk : C -> K -> bool) k li : option V :=
  match li with
  | [] => None
  | (hd, v) :: tl => if fk k hd then Some v else find_kv fk k tl
  end.

Theorem reflect_find_kv : forall {K V} fk k v li,
  (forall a b, Bool.reflect (a = b) (fk a b)) ->
  @FindKV K V k v li <-> find_kv fk k li = Some v.
Proof.
  split; intros.
  - generalize dependent fk. induction H; intros; simpl in *.
    + destruct (X k k). { reflexivity. } contradiction n. reflexivity.
    + destruct (X k hk). { subst. contradiction H. reflexivity. } apply IHFindKV. assumption.
  - generalize dependent fk. generalize dependent k. generalize dependent v.
    induction li; intros; simpl in *. { discriminate H. }
    destruct a. destruct (X k k0). { invert H. constructor. }
    constructor. { assumption. } eapply IHli. { apply X. } assumption.
Qed.

Theorem find_kv_none : forall {K V} fk k li,
  (forall a b, Bool.reflect (a = b) (fk a b)) ->
  find_kv fk k li = None <-> forall v, ~@FindKV K V k v li.
Proof.
  split; intros.
  - intro C. generalize dependent fk. induction C; intros; simpl in *.
    + destruct (X k k). { discriminate H. } contradiction n. reflexivity.
    + destruct (X k hk). { contradiction H. } eapply IHC. { apply X. } assumption.
  - generalize dependent fk. generalize dependent k. induction li; intros; simpl in *. { reflexivity. }
    destruct a as [ka va]. destruct (X k ka). { subst. contradiction (H va). constructor. }
    apply IHli; [| assumption]. intros v C. assert (A : FindKV k v ((ka, va) :: li)). { constructor; assumption. }
    apply H in A as [].
Qed.

Theorem not_in_fst_find_none : forall {K V} fk k li,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  (~In k (map fst li)) <-> @find_kv K V K fk k li = None.
Proof.
  split.
  - generalize dependent fk. generalize dependent k. induction li; intros; simpl in *. { reflexivity. }
    destruct a as [ka va]. simpl in *. apply Decidable.not_or in H as [Hk Hi].
    destruct (X k ka). { contradiction Hk. symmetry. assumption. }
    eapply (find_kv_none _ _ _ X). eapply (not_in_fst_find _ _ _ X). assumption.
  - generalize dependent fk. generalize dependent k. induction li; intros; intros []; destruct a as [ka va]; simpl in *; subst.
    + destruct (X k k). { discriminate H. } apply n. reflexivity.
    + destruct (X k ka). { discriminate H. } apply (IHli _ _ X) in H. apply H in H0 as [].
Qed.

Lemma find_kv_weaken : forall {K V} k v li weaken,
  @FindKV K V k v li ->
  FindKV k v (li ++ weaken).
Proof. intros. generalize dependent weaken. induction H; intros; simpl in *; constructor. { assumption. } apply IHFindKV. Qed.

Lemma find_kv_app : forall {K V} k v hd tl fk,
  (forall a b : K, Bool.reflect (a = b) (fk a b)) ->
  @FindKV K V k v (hd ++ tl) <->
  (FindKV k v hd \/ (FindKV k v tl /\ forall v', ~FindKV k v' hd)).
Proof.
  split; intros.
  - generalize dependent k. generalize dependent v. generalize dependent tl.
    induction hd; intros; simpl in *. { right. split. { assumption. } intros v' C. invert C. } invert H. { left. constructor. }
    specialize (IHhd _ _ _ H3) as [IH | [IH1 IH2]]. { left. constructor; assumption. } right. split. { assumption. }
    intros v' C. invert C. { apply H2. reflexivity. } apply IH2 in H5 as [].
  - destruct H as [H | [H1 H2]]. { apply find_kv_weaken. assumption. } induction hd. { assumption. }
    destruct a. destruct (X k k0). { subst. contradiction (H2 v0). constructor. } constructor. { assumption. }
    apply IHhd. intros v' C. specialize (H2 v'). apply H2. constructor; assumption.
Qed.

Lemma find_kv_exchange : forall {K V} pre k1 v1 k2 v2 post k v,
  k1 <> k2 ->
  @FindKV K V k v (pre ++ (k1, v1) :: (k2, v2) :: post) ->
  FindKV k v (pre ++ (k2, v2) :: (k1, v1) :: post).
Proof.
  intros. remember (pre ++ (k1, v1) :: (k2, v2) :: post) as li eqn:El. generalize dependent pre. generalize dependent k1.
  generalize dependent v1. generalize dependent k2. generalize dependent v2. generalize dependent post.
  induction H0; intros; subst; simpl in *. { destruct pre; invert El; constructor. { assumption. } constructor. }
  destruct pre; invert El. { invert H0; constructor. { assumption. } constructor; assumption. }
  constructor. { assumption. } apply IHFindKV. { assumption. } reflexivity.
Qed.
