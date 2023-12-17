(* CRUCIAL NOTE: Typing is not unique: many types could type the same term.
 * So we want typechecking to return `Some` iff it's typeable, but the types themselves may differ. *)

From Adam Require Import
  Invert
  OptionBind
  Snoc
  Subst
  Terms
  TypecheckDef
  Types.

Theorem typecheck_weak_snoc : forall hd tl t t' ctx',
  typecheck tl t = Some (t', ctx') ->
  typecheck (snoc hd tl) t = Some (t', snoc hd ctx').
Proof.
  simpl. intros. destruct hd as [v vt].
  generalize dependent v. generalize dependent vt. generalize dependent tl.
  generalize dependent t'. generalize dependent ctx'.
  induction t; intros; try discriminate.
  - destruct tl; try discriminate H. destruct p. simpl in *. destruct (eqb id s); invert H. reflexivity.
  - invert H. simpl. reflexivity.
  - simpl in *. destruct (atom_id t2) eqn:E2; try discriminate H.
    destruct (eqb id s) eqn:Es; try discriminate H. apply eqb_eq in Es. subst.
    destruct arg; [destruct (typecheck ((s0, t1) :: tl) t2) eqn:Et | destruct (typecheck tl t2) eqn:Et];
    try discriminate H; destruct p; invert H; eapply IHt2 in Et; simpl in Et; rewrite Et; reflexivity.
  - simpl in *. destruct arg; [destruct (typecheck ((s, t1) :: tl) t2) eqn:Et | destruct (typecheck tl t2) eqn:Et];
    try discriminate H; destruct p; invert H; eapply IHt2 in Et; simpl in Et; rewrite Et; reflexivity.
  - simpl in *. destruct (typecheck tl t1) eqn:Et1; try discriminate H. destruct p.
    destruct t; try discriminate H. destruct (typecheck l t2) eqn:Et2; try discriminate H. destruct p.
    destruct (eq_term t3 t) eqn:Ee; try discriminate H; destruct arg; [destruct (subst s t2 t4) eqn:Es |];
    invert H; eapply IHt1 in Et1; rewrite Et1; eapply IHt2 in Et2;
    rewrite Et2; rewrite Ee; try rewrite Es; reflexivity.
Qed.

Theorem typecheck_weakening : forall ctx ext t t' ctx',
  typecheck ctx t = Some (t', ctx') ->
  typecheck (ctx ++ ext) t = Some (t', ctx' ++ ext).
Proof.
  intros ctx ext. generalize dependent ctx.
  induction ext; intros; simpl in *. { repeat rewrite app_nil_r. assumption. }
  repeat rewrite app_hd_snoc. apply IHext. eapply typecheck_weak_snoc. assumption.
Qed.

(*
Theorem typecheck_length_decr : forall ctx t t' ctx',
  typecheck ctx t = Some (t', ctx') ->
  Datatypes.length ctx' <= Datatypes.length ctx.
Proof.
  intros ctx t. generalize dependent ctx. induction t; intros; try discriminate.
  - simpl in *. destruct ctx; try discriminate H. destruct p.
    destruct (eqb id s); invert H. simpl. repeat constructor.
  - invert H. constructor.
  - simpl in *. destruct (atom_id t2) eqn:Ea; try discriminate H.
    destruct (eqb id s) eqn:E; try discriminate H. apply eqb_eq in E. subst. destruct arg;
    [destruct (typecheck ((s0, t1) :: ctx) t2) eqn:Et | destruct (typecheck ctx t2) eqn:Et];
    try discriminate H; destruct p; invert H; apply IHt2 in Et; try apply Et. simpl in *.
Qed.
*)

(*
Theorem typecheck_desnoc : forall ctx ctx' t t' etc etc',
  desnoc ctx = Some ctx' ->
  desnoc etc = Some etc' ->
  typecheck ctx t = Some (t', etc) ->
  typecheck ctx' t = Some (t', etc').
Proof.
  intros ctx ctx' t. generalize dependent ctx'. generalize dependent ctx.
  induction t; intros; simpl in *; try discriminate.
  - destruct ctx; try discriminate H1. destruct p. destruct (eqb id s) eqn:E; invert H1. apply eqb_eq in E.
    simpl in *. rewrite H0 in H. invert H. rewrite eqb_refl. reflexivity.
  - invert H1. rewrite H0 in H. invert H. reflexivity.
  - destruct (atom_id t2); try discriminate H1. destruct (eqb id s); try discriminate H1.
    destruct arg; [destruct (typecheck ((s0, t1) :: ctx) t2) eqn:E | destruct (typecheck ctx t2) eqn:E];
    try destruct p; invert H1; erewrite IHt2; try reflexivity;
    try apply H0; try apply E; simpl; rewrite H; reflexivity.
  - destruct arg; [destruct (typecheck ((s, t1) :: ctx) t2) eqn:E | destruct (typecheck ctx t2) eqn:E];
    try destruct p; invert H1; erewrite IHt2; try reflexivity;
    try apply H0; try apply E; simpl; rewrite H; reflexivity.
  - destruct (typecheck ctx t1) eqn:E1; try discriminate H1. destruct p. destruct t; try discriminate H1.
    destruct (typecheck l t2) eqn:E2; try discriminate H1. destruct p.
    destruct (eq_term t3 t) eqn:E; try discriminate H1. destruct l; simpl in *.
    + destruct arg; [destruct (subst s t2 t4) eqn:Es |]; invert H1.
    clear IHt2.
    destruct arg; [destruct (subst s t2 t4) eqn:Es |]; invert H1.
    erewrite IHt1; try reflexivity; try apply E1; try apply H; simpl.
    try rewrite E2; try rewrite E; try rewrite Es; try reflexivity. admit. admit.
Qed.

Theorem typecheck_unweaken : forall ctx t t' ctx',
  typecheck ctx t = Some (t', ctx') ->
  exists mctx, ctx = mctx ++ ctx' /\ typecheck mctx t = Some (t', []).
Proof.
  intros. generalize dependent ctx. generalize dependent t. generalize dependent t'.
  induction ctx'; intros; simpl in *. { exists ctx. split. { rewrite app_nil_r. reflexivity. } assumption. }
  induction ctx.
  - induction t. simpl in H.
Qed.

Inductive BeginsWith {T} : list T -> list T -> Prop :=
  | BeginsWithNil : forall li,
      BeginsWith [] li
  | BeginsWithCons : forall hd tl li,
      BeginsWith tl li ->
      BeginsWith (hd :: tl) (hd :: li)
  .
Theorem begins_with_refl : forall {T} li, @BeginsWith T li li.
Proof. induction li. { constructor. } constructor. assumption. Qed.
Theorem begins_with_eq_append : forall {T} pre post,
  @BeginsWith T pre post <-> exists ext, post = pre ++ ext.
Proof.
  intros T pre. induction pre; intros; simpl in *.
  - split; intros. { exists post. reflexivity. } constructor.
  - split; intros. { invert H. apply IHpre in H3. destruct H3. rewrite H. exists x. reflexivity. }
    destruct H. subst. constructor. apply IHpre. exists x. reflexivity.
Qed.

(* Note that we can't say `typecheck ctx t <> Some (ty, []) -> ~Typed ctx t ty`,
 * since the typing relation may not be unique: `typecheck` chooses only one type.
 * We also can't say `~Typed ctx t ty -> typecheck ctx t = None`,
 * since some term may be typable with some context left over. *)
(* TODO: Faithfully follow the above and prove that `typecheck` picks the SMALLEST type! *)
Definition TypecheckCorrectOn : term -> Prop := fun t => forall ctx,
  (typecheck ctx t = None -> ~exists ty, Typed ctx t ty) /\ forall ty,
  (typecheck ctx t = Some (ty, []) -> Typed ctx t ty) /\
  (* (Typed ctx t ty -> exists ty', typecheck ctx t = Some (ty', [])) /\ *)
  (Typed ctx t ty -> typecheck ctx t = Some (ty, [])) /\
  (~Typed ctx t ty -> typecheck ctx t <> Some (ty, [])).
Arguments TypecheckCorrectOn t/.
Ltac tcintros := repeat split; intros; try intros [ty C]; try intro C; try discriminate.

Lemma typecheck_correct_void : TypecheckCorrectOn TmVoid.
Proof. tcintros. { invert C. } invert H. Qed.

Lemma typecheck_correct_star : forall lvl, TypecheckCorrectOn (TmStar lvl).
Proof. tcintros. { invert C. } invert H. Qed.

Lemma typecheck_correct_vars : forall id, TypecheckCorrectOn (TmVarS id).
Proof.
  tcintros.
  - invert C. simpl in H. rewrite eqb_refl in H. discriminate H.
  - destruct ctx; try discriminate H. destruct p. simpl in *.
    destruct (eqb id s) eqn:E; invert H. apply eqb_eq in E. subst. constructor.
  - invert H. simpl in *. rewrite eqb_refl. reflexivity.
  - destruct ctx; try discriminate C. destruct p. simpl in *.
    destruct (eqb id s) eqn:E; invert C. apply eqb_eq in E. subst. contradiction H. constructor.
Qed.

Lemma typecheck_correct_atom : forall id lvl, TypecheckCorrectOn (TmAtom id lvl).
Proof.
  tcintros.
  - invert H. constructor.
  - invert H. reflexivity.
  - invert C. contradiction H. constructor.
Qed.

Lemma typecheck_correct_pack : forall id arg t curry,
  TypecheckCorrectOn curry ->
  TypecheckCorrectOn (TmPack id arg t curry).
Proof.
  tcintros.
  - simpl in H0. invert C; apply reflect_atom_id in H8; rewrite H8 in H0; rewrite eqb_refl in H0;
    [destruct (typecheck ctx curry) eqn:Et | destruct (typecheck ((arg0, t) :: ctx) curry) eqn:Et];
    try destruct p; try discriminate H0; apply H in Et; contradiction Et; eexists; apply H7.
  - simpl in H0. destruct (atom_id curry) eqn:Ea; try discriminate H0. apply reflect_atom_id in Ea.
    destruct (eqb id s) eqn:Es; try discriminate H0. apply eqb_eq in Es. subst.
    destruct arg; [destruct (typecheck ((s0, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try discriminate H0; destruct p; invert H0; [specialize (H ((s0, t) :: ctx)) | specialize (H ctx)];
    destruct H; specialize (H0 t0); destruct H0; apply H0 in Et; constructor; assumption.
  - invert H0; simpl; apply reflect_atom_id in H8; rewrite H8;
    rewrite eqb_refl; apply H in H7; rewrite H7; reflexivity.
  - simpl in C. destruct (atom_id curry) eqn:Ea; try discriminate C. apply reflect_atom_id in Ea.
    destruct (eqb id s) eqn:E; try discriminate C. apply eqb_eq in E. subst.
    destruct arg; [destruct (typecheck ((s0, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try destruct p; try discriminate; invert C;
    [specialize (H ((s0, t) :: ctx)) as [_ H] | specialize (H ctx) as [_ H]];
    specialize (H t0) as [H _]; apply H in Et; contradiction H0; constructor; assumption.
Qed.

Lemma typecheck_correct_fora : forall arg t curry,
  TypecheckCorrectOn curry ->
  TypecheckCorrectOn (TmForA arg t curry).
Proof.
  tcintros.
  - simpl in H0. invert C; apply H in H6; rewrite H6 in H0; discriminate H0.
  - simpl in H0. destruct arg;
    [destruct (typecheck ((s, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try destruct p; try discriminate; invert H0; constructor;
    [specialize (H ((s, t) :: ctx)) as [_ H] | specialize (H ctx) as [_ H]];
    specialize (H t0) as [H _]; apply H in Et; assumption.
  - invert H0; apply H in H6; simpl; rewrite H6; eexists; reflexivity.
  - simpl in C. destruct arg;
    [destruct (typecheck ((s, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try destruct p; try discriminate; invert C;
    [specialize (H ((s, t) :: ctx)) as [_ H] | specialize (H ctx) as [_ H]];
    specialize (H t0) as [H _]; apply H in Et; contradiction H0; constructor; assumption.
Qed.

Lemma typecheck_correct_appl : forall f x,
  TypecheckCorrectOn f ->
  TypecheckCorrectOn x ->
  TypecheckCorrectOn (TmAppl f x).
Proof.
  tcintros.
  - simpl in H1. invert C;
    apply H in H4; eapply typecheck_weakening in H4; simpl in H4; rewrite H4 in H1;
    [apply H0 in H6; rewrite H6 in H1 | apply H0 in H5; rewrite H5 in H1];
    rewrite eq_term_refl in H1; [| apply reflect_subst in H9; rewrite H9 in H1]; discriminate H1.
  - simpl in H1. destruct (typecheck ctx f) eqn:Ef; try discriminate H1. destruct p.
    destruct t; try discriminate H1. destruct (typecheck c x) eqn:Ex; try discriminate H1. destruct p.
    destruct (eq_term t1 t) eqn:E; try discriminate H1. destruct arg.
    + destruct (subst s x t2); invert H1.
Qed.

Theorem typecheck_correct : forall t, TypecheckCorrectOn t.
Proof.
  induction t.
  - apply typecheck_correct_void.
  - apply typecheck_correct_star.
  - apply typecheck_correct_vars.
  - apply typecheck_correct_atom.
  - apply typecheck_correct_pack. assumption.
  - apply typecheck_correct_fora. assumption.
  - Admitted.
*)
