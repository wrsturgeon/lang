From Coq Require Export
  List
  Sorting.Permutation
  String
  Program.Wf.
Export ListNotations.
From Lang Require Import
  Invert
  Snoc.

(* note that this is nondeterministic: no head non-equality check *)
Inductive Remove {T} x : list T -> list T -> Prop :=
  | RemoveHead : forall tl,
      Remove x (x :: tl) tl
  | RemoveSkip : forall hd tl tl',
      Remove x tl tl' ->
      Remove x (hd :: tl) (hd :: tl')
  .

Lemma cons_app : forall {T} (hd : T) tl, hd :: tl = [hd] ++ tl. Proof. reflexivity. Qed.

Lemma remove_app_r : forall {T} (x : T) a b out,
  Remove x b out ->
  Remove x (a ++ b) (a ++ out).
Proof.
  intros T x a. generalize dependent x.
  induction a; intros; [| apply RemoveSkip; apply IHa]; assumption.
Qed.

Lemma remove_app_l : forall {T} (x : T) a b out,
  Remove x a out ->
  Remove x (a ++ b) (out ++ b).
Proof. intros. generalize dependent b. induction H; intros; simpl in *; constructor. apply IHRemove. Qed.

Lemma remove_app_iff : forall {T} (x : T) a out,
  Remove x a out <-> exists hd tl, (a = hd ++ x :: tl /\ out = hd ++ tl).
Proof.
  split; intros.
  - induction H. { exists []. exists tl. split; reflexivity. }
    destruct IHRemove as [h [t [IH1 IH2]]]. subst. exists (hd :: h). exists t. split; reflexivity.
  - destruct H as [hd [tl [H1 H2]]]. subst. apply remove_app_r. constructor.
Qed.

Lemma remove_still_in : forall {T} (x : T) y pre post,
  x <> y ->
  Remove x pre post ->
  In y pre ->
  In y post.
Proof.
  intros T x y pre post Hxy Hr Hi. generalize dependent y.
  induction Hr; intros; simpl in *. { destruct Hi. { subst. contradiction Hxy. reflexivity. } assumption. }
  destruct Hi. { left. assumption. } right. apply IHHr; assumption.
Qed.

Lemma remove_not_in : forall {T} (x : T) y pre post,
  Remove x pre post ->
  ~In y pre ->
  ~In y post.
Proof.
  intros T x y pre post Hr Hi C. generalize dependent y.
  induction Hr; intros; simpl in *; apply Decidable.not_or in Hi as [Hxy Hi]. { apply Hi. assumption. }
  destruct C. { subst. contradiction Hxy. reflexivity. } apply (IHHr y); assumption.
Qed.

Lemma remove_in : forall {T} (x : T) y pre post,
  In y post ->
  Remove x pre post ->
  In y pre.
Proof.
  intros. generalize dependent y. induction H0; intros; simpl in *. { right. assumption. }
  destruct H; [left | right; apply IHRemove]; assumption.
Qed.

Lemma remove_in_pre : forall {T} (x : T) pre post,
  Remove x pre post ->
  In x pre.
Proof. intros. induction H. { left. reflexivity. } right. assumption. Qed.

Inductive DupFrom {T} (src : list T) : list T -> list T -> Prop :=
  | DupFromNil :
      DupFrom src [] src
  | DupFromCopy : forall x src' out out',
      DupFrom src out' src' ->
      In x src ->
      Remove x out out' ->
      DupFrom src out src'
  | DupFromTake : forall x src' src'' out out',
      DupFrom src' out' src'' ->
      Remove x src src' ->
      Remove x out out' ->
      DupFrom src out src''
  .
Arguments DupFrom {T} src out src'.
Ltac dup_from_nil := apply DupFromNil.
Ltac dup_from_copy := eapply DupFromCopy; [| | apply RemoveHead]; [| repeat (try (left; reflexivity); right)].
Ltac dup_from_take := eapply DupFromTake; [| | apply RemoveHead]; [| repeat constructor].
Ltac dup_from := try dup_from_nil; try (dup_from_take; dup_from); dup_from_copy; dup_from.

Example dup_from_12345 : DupFrom [1;2;3;4;5] [1;1;1;1;1;1;4;2;5;3;3] [1;3;5].
Proof.
  dup_from_copy. dup_from_copy. dup_from_copy. dup_from_copy. dup_from_copy. dup_from_copy.
  dup_from_take. dup_from_take. dup_from_copy. dup_from_copy. dup_from_copy. dup_from_nil.
Qed.

Theorem dup_from_app : forall {T} (a : list T) b,
  DupFrom (a ++ b) a b.
Proof. intros T a. induction a; intros; simpl in *; [| eapply DupFromTake; [apply IHa | |]]; constructor. Qed.

Fixpoint has_with {A B} (f : A -> B -> bool) x li :=
  match li with
  | [] => false
  | hd :: tl => if f x hd then true else has_with f x tl
  end.

Theorem has_in : forall {T} x (f : T -> T -> bool) li,
  (forall a b, f a b = true <-> a = b) ->
  Bool.reflect (In x li) (has_with f x li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { constructor. intros []. }
  destruct (f x a) eqn:E. { apply H in E. subst. constructor. left. reflexivity. }
  specialize (IHli x). destruct IHli; constructor. { right. assumption. }
  intros [C1 | C2]. { subst. assert (A : x = x). { reflexivity. } apply H in A. rewrite A in E. discriminate E. }
  apply n. assumption.
Qed.

Theorem has_in_iff : forall {T} x (f : T -> T -> bool) li,
  (forall a b, f a b = true <-> a = b) ->
  In x li <-> has_with f x li = true.
Proof. intros. apply Bool.reflect_iff. apply has_in. assumption. Qed.

Theorem has_in_iff_not : forall {T} x (f : T -> T -> bool) li,
  (forall a b, f a b = true <-> a = b) ->
  ~In x li <-> has_with f x li = false.
Proof.
  split; intros.
  - destruct (has_in x f li); try reflexivity. { assumption. } apply H0 in i. destruct i.
  - intro C. eapply has_in_iff in C; [| apply H]. rewrite H0 in C. discriminate C.
Qed.

Theorem has_app : forall {A B} x (f : A -> B -> bool) a b,
  has_with f x (a ++ b) = orb (has_with f x a) (has_with f x b).
Proof.
  intros A B x f a. generalize dependent A. induction a; intros; simpl in *. { reflexivity. }
  destruct (f x a). { reflexivity. } apply IHa.
Qed.

(* TODO: faster version (the intuitive one doesn't seem to be correct) *)
Fixpoint dup_from_src_with {T} (f : T -> T -> bool) out src' :=
  match out with
  | [] => src'
  | hd :: tl =>
      let recursed := dup_from_src_with f tl src' in
      if has_with f hd recursed then recursed else hd :: recursed
  end.

Lemma dup_from_src_works : forall {T} (f : T -> T -> bool) out src',
  (forall a b : T, f a b = true <-> a = b) ->
  DupFrom (dup_from_src_with f out src') out src'.
Proof.
  induction out; intros; simpl in *. { constructor. }
  destruct (has_in a f (dup_from_src_with f out src')); [assumption | |].
  - eapply DupFromCopy; [apply IHout; assumption | | constructor]. assumption.
  - eapply DupFromTake; [| constructor | constructor]. apply IHout. assumption.
Qed.

(* and the above is probably minimal, but that turns out to be very difficult to prove *)
