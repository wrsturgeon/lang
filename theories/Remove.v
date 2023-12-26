From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  Count
  Invert.

(* This needs to be deterministic. If not, free variables are nondeterministic, which is disastrous. *)
Inductive Remove {T} x : list T -> list T -> Prop :=
  | RemoveHead : forall tl,
      Remove x (x :: tl) tl
  | RemoveSkip : forall hd tl tl',
      x <> hd ->
      Remove x tl tl' ->
      Remove x (hd :: tl) (hd :: tl')
  .
Ltac autoremove := repeat constructor; intro; discriminate.

Example remove_12345 : Remove 3 [1;2;3;4;5] [1;2;4;5]. Proof. autoremove. Qed.

Lemma cons_app : forall {T} (hd : T) tl, hd :: tl = [hd] ++ tl. Proof. reflexivity. Qed.

Lemma remove_app_r : forall {T} (x : T) a b out,
  ~In x a ->
  Remove x b out ->
  Remove x (a ++ b) (a ++ out).
Proof.
  intros T x a. generalize dependent x.
  induction a; intros. { assumption. }
  simpl in *. apply Decidable.not_or in H as [H1 H2].
  apply RemoveSkip. { symmetry. assumption. } apply IHa; assumption.
Qed.

Lemma remove_app_l : forall {T} (x : T) a b out,
  Remove x a out ->
  Remove x (a ++ b) (out ++ b).
Proof. intros. generalize dependent b. induction H; intros; simpl in *; constructor. { assumption. } apply IHRemove. Qed.

Lemma remove_app_iff : forall {T} (x : T) a out,
  Remove x a out <-> exists hd tl, (a = hd ++ x :: tl /\ out = hd ++ tl /\ ~In x hd).
Proof.
  split; intros.
  - induction H. { exists []. exists tl. repeat split. intros []. }
    destruct IHRemove as [h [t [IH1 [IH2 IH3]]]]. subst. exists (hd :: h). exists t. repeat split.
    intros [C | C]. { subst. apply H. reflexivity. } apply IH3. assumption.
  - destruct H as [hd [tl [H1 [H2 H3]]]]. subst. apply remove_app_r. { assumption. } constructor.
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
  destruct H1; [left | right; apply IHRemove]; assumption.
Qed.

Lemma remove_in_pre : forall {T} (x : T) pre post,
  Remove x pre post ->
  In x pre.
Proof. intros. induction H. { left. reflexivity. } right. assumption. Qed.

Lemma remove_map_fst : forall {A B} a b pre post,
  @Remove (A * B) (a, b) pre post ->
  Remove a (map fst pre) (map fst post).
Proof.
  intros. remember (a, b) as ab eqn:Eab. generalize dependent a. generalize dependent b.
  induction H; intros; subst; simpl in *. { constructor. } destruct hd. simpl. constructor. { Abort.

Theorem remove_deterministic : forall {T} x pre post post',
  @Remove T x pre post ->
  Remove x pre post' ->
  post = post'.
Proof.
  intros. generalize dependent post'. induction H; intros; simpl in *.
  - invert H0. { reflexivity. } contradiction H2. reflexivity.
  - invert H1. { contradiction H. reflexivity. } f_equal. apply IHRemove. assumption.
Qed.

Theorem remove_count : forall {T} x pre post n,
  @Remove T x pre post ->
  Count x post n ->
  Count x pre (S n).
Proof.
  intros. generalize dependent n. induction H; intros; simpl in *; constructor; try assumption.
  apply IHRemove. invert H1. { contradiction H. reflexivity. } assumption.
Qed.
