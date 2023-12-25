From Coq Require Export
  List.
Export ListNotations.

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

Lemma remove_map_fst : forall {A B} a b pre post,
  @Remove (A * B) (a, b) pre post ->
  Remove a (map fst pre) (map fst post).
Proof.
  intros. remember (a, b) as ab eqn:Eab. generalize dependent a. generalize dependent b.
  induction H; intros; subst; simpl in *. { constructor. } destruct hd. simpl. constructor. eapply IHRemove. reflexivity.
Qed.
