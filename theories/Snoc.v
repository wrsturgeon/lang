From Coq Require Export
  Lists.List.
Export ListNotations.

Fixpoint snoc {T} (x : T) li :=
  match li with
  | [] => [x]
  | hd :: tl => hd :: snoc x tl
  end.
Definition flip_snoc := fun {T} li x => @snoc T x li.
Arguments flip_snoc {T} li x/.

Lemma app_hd_snoc : forall {T} pre hd tl,
  pre ++ hd :: tl = (@snoc T hd pre) ++ tl.
Proof.
  intros T pre. induction pre; intros; simpl in *. { reflexivity. }
  rewrite IHpre. reflexivity.
Qed.

Lemma snoc_app_tl : forall {T} (x : T) li,
  snoc x li = li ++ [x].
Proof. intros. generalize dependent x. induction li; intros; simpl; [| rewrite IHli]; reflexivity. Qed.

Fixpoint desnoc {T} (li : list T) :=
  match li with
  | [] => None
  | hd :: tl => match desnoc tl with None => Some [] | Some etc => Some (hd :: etc) end
  end.

Example desnoc_12345 : desnoc [1;2;3;4;5] = Some [1;2;3;4]. Proof. reflexivity. Qed.
Example desnoc_nil : @desnoc nat [] = None. Proof. reflexivity. Qed.

Theorem desnoc_none_iff_nil : forall {T} li,
  @desnoc T li = None <-> li = [].
Proof.
  split; intros.
  - destruct li. { reflexivity. } simpl in *. destruct (desnoc li); discriminate H.
  - subst. reflexivity.
Qed.
