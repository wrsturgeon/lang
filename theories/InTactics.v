From Coq Require Export
  List.
Export ListNotations.

Ltac auto_in := repeat (try (left; reflexivity); right); fail.
Example auto_in_12345 : In 3 [1;2;3;4;5]. Proof. auto_in. Qed.
Example auto_in_12345_fail : In 9 [1;2;3;4;5]. Proof. Fail auto_in. Abort.

Ltac not_in H := repeat (destruct H as [H | H]; [discriminate H |]); contradiction H.
Example not_in_12345 : ~In 9 [1;2;3;4;5]. Proof. intro C. not_in C. Qed.
Example not_in_12345_fail : ~In 3 [1;2;3;4;5]. Proof. intro C. Fail not_in C. Abort.

Theorem in_map_fst : forall {A B} a b li,
  @In (A * B) (a, b) li ->
  In a (map fst li).
Proof.
  induction li; intros; simpl in *; destruct H.
  - subst. left. reflexivity.
  - right. apply IHli. assumption.
Qed.

Theorem not_in_map_fst : forall {A B} a b li,
  ~In a (map fst li) ->
  ~@In (A * B) (a, b) li.
Proof.
  induction li; intros; simpl in *. { assumption. }
  apply Decidable.not_or in H as [H1 H2]. intros [C | C].
  - subst. apply H1. reflexivity.
  - apply in_map_fst in C. apply H2 in C as [].
Qed.

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

Lemma in_map_fst_app : forall {K V} k (a b : list (K * V)),
  In k (map fst (a ++ b)) <-> (In k (map fst a) \/ In k (map fst b)).
Proof.
  split; intros.
  - generalize dependent k. generalize dependent b. induction a; intros. { right. assumption. }
    destruct a. simpl in *. destruct H. { left. left. assumption. }
    apply or_assoc. right. apply IHa. assumption.
  - generalize dependent k. generalize dependent b. induction a; intros. { destruct H. { destruct H. } assumption. }
    simpl in *. apply or_assoc in H as [H | H]. { left. assumption. } right. apply IHa. assumption.
Qed.
