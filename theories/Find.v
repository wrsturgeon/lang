From Coq Require Export
  List.
Export ListNotations.

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
