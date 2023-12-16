(* CRUCIAL NOTE: Typing is not unique: many types could type the same term.
 * So we want typechecking to return `Some` iff it's typeable, but the types themselves may differ. *)

From Adam Require Import
  Invert
  OptionBind
  Subst
  Terms
  Types.

Fixpoint lookup_type ctx : string -> option term := fun x =>
  match ctx with
  | [] => None
  | (s, t) :: tl => if eqb x s then Some t else lookup_type tl x
  end.

(*
Fixpoint try_remove {X L} (eqf : X -> L -> bool) x li :=
  match li with
  | [] => None
  | hd :: tl => if eqf x hd then Some tl else option_map (cons hd) (try_remove eqf x tl)
  end.

Definition fst_eq : string -> (string * term) -> bool := fun x pair =>
  match pair with (term, type) => eqb x term end.
*)

(*
(* TODO: This is horrendous performance-wise: find a better way! *)
Fixpoint brute_force_split {X Y} (f : list X -> list X -> option Y) (lp rp : list X) : option Y :=
  match f lp rp with
  | Some y => Some y
  | None =>
      match rp with
      | [] => None
      | hd :: tl => brute_force_split f (hd :: lp) tl
      end
  end.
Search (list _ -> nat).
Theorem brute_force_split_works : forall {X Y} f (la lb lc : list X) (y : Y),
  (lc = la ++ lb /\ f la lb = Some y /\ ~exists sa sb, (
    length sa < length la /\ lc = sa ++ sb /\ f sa sb = Some y)) <->
  brute_force_split f [] lb = Some y.
Proof.
  split; intros.
  - destruct H as [Hl [Hf He]]. generalize dependent Y. generalize dependent la. generalize dependent lc.
    induction lb; intros; simpl in *.
    + destruct la. { rewrite Hf. reflexivity. } subst. destruct (f [] []) eqn:E. { contradiction He [] []. reflexivity. } simpl. destruct lb; simpl; rewrite Hf; reflexivity.
    + destruct lc; [discriminate Hl |]. injection Hl as Hl. eapply IHla; [apply H | |]. destruct lb; simpl.
  intros X Y f la. generalize dependent Y. induction la; intros; simpl in *.
  - 
Qed.
*)

(* Semantics:
 * `None` means never typable, no matter the context;
 * `Some (ty, ctx)` means typed with `ctx` left over *)
Fixpoint typecheck (ctx : context) (t : term) : option (term * context) :=
  match t with
  | TmVarS x => match ctx with [] => None | (s, ty) :: tl => if eqb x s then Some (ty, tl) else None end
  | TmAtom id lvl => Some (TmAtom id (S lvl), ctx)
  (* | TmAtom id lvl => match ctx with [] => Some (TmAtom id (S lvl), ctx) | _ :: _ => None end *)
  | TmPack id arg ty curry =>
      let ectx := match arg with None => ctx | Some s => (s, ty) :: ctx end in
      match atom_id curry with
      | None => None
      | Some aid =>
          if eqb id aid then
            match typecheck ectx curry with
            | Some (ct, etc) => Some (TmForA arg ty ct, etc)
            | _ => None
            end
          else None
      end
  | TmForA arg ty curry =>
      let ectx := match arg with None => ctx | Some s => (s, ty) :: ctx end in
      match typecheck ectx curry with
      | None => None
      | Some (ct, etc) => Some (TmForA arg ty ct, etc)
      end
  | TmAppl f x =>
      match typecheck ctx f with
      | Some (TmForA arg ty curry, leftover) =>
          let if_successful := (fun y => match y with (tx, etc) =>
            if eq_term ty tx then
              match arg with
              | None => Some (curry, etc)
              | Some s =>
                  match subst s x curry with
                  | Unused => None
                  | Used t => Some (t, etc)
                  end
              end
            else None
          end) in option_bind if_successful (typecheck leftover x)
      | _ => None
      end
  | _ => None
  end.

Fixpoint snoc {T} (x : T) li :=
  match li with
  | [] => [x]
  | hd :: tl => hd :: snoc x tl
  end.
Definition flip_snoc := fun {T} li x => @snoc T x li.
Arguments flip_snoc {T} li x/.

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
    destruct t; try discriminate H. destruct (typecheck c t2) eqn:Et2; try discriminate H. destruct p.
    destruct (eq_term t3 t) eqn:Ee; try discriminate H; destruct arg; [destruct (subst s t2 t4) eqn:Es |];
    invert H; eapply IHt1 in Et1; rewrite Et1; eapply IHt2 in Et2;
    rewrite Et2; rewrite Ee; try rewrite Es; reflexivity.
Qed.

Lemma app_hd_snoc : forall {T} pre hd tl,
  pre ++ hd :: tl = (@snoc T hd pre) ++ tl.
Proof.
  intros T pre. induction pre; intros; simpl in *. { reflexivity. }
  rewrite IHpre. reflexivity.
Qed.
Theorem typecheck_weakening : forall ctx ext t t' ctx',
  typecheck ctx t = Some (t', ctx') ->
  typecheck (ctx ++ ext) t = Some (t', ctx' ++ ext).
Proof.
  intros ctx ext. generalize dependent ctx.
  induction ext; intros; simpl in *. { repeat rewrite app_nil_r. assumption. }
  repeat rewrite app_hd_snoc. apply IHext. eapply typecheck_weak_snoc. assumption.
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
Definition TypecheckCorrectOn : term -> Prop := fun t => forall ctx,
  (typecheck ctx t = None -> ~exists ty, Typed ctx t ty) /\ forall ty,
  (typecheck ctx t = Some (ty, []) -> Typed ctx t ty) /\
  (Typed ctx t ty -> exists ty', typecheck ctx t = Some (ty', [])) /\
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
  - invert H. simpl in *. rewrite eqb_refl. eexists. reflexivity.
  - destruct ctx; try discriminate C. destruct p. simpl in *.
    destruct (eqb id s) eqn:E; invert C. apply eqb_eq in E. subst. contradiction H. constructor.
Qed.

Lemma typecheck_correct_atom : forall id lvl, TypecheckCorrectOn (TmAtom id lvl).
Proof.
  tcintros.
  - invert H. constructor.
  - invert H. eexists. reflexivity.
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
  - invert H0; simpl; apply H in H7; destruct H7; apply reflect_atom_id in H8; rewrite H8;
    rewrite eqb_refl; rewrite H0; eexists; reflexivity.
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
  - simpl in H0. invert C; apply H in H6; destruct H6 as [ty' H6]; rewrite H6 in H0; discriminate H0.
  - simpl in H0. destruct arg;
    [destruct (typecheck ((s, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try destruct p; try discriminate; invert H0; constructor;
    [specialize (H ((s, t) :: ctx)) as [_ H] | specialize (H ctx) as [_ H]];
    specialize (H t0) as [H _]; apply H in Et; assumption.
  - invert H0; apply H in H6; destruct H6; simpl; rewrite H0; eexists; reflexivity.
  - simpl in C. destruct arg;
    [destruct (typecheck ((s, t) :: ctx) curry) eqn:Et | destruct (typecheck ctx curry) eqn:Et];
    try destruct p; try discriminate; invert C;
    [specialize (H ((s, t) :: ctx)) as [_ H] | specialize (H ctx) as [_ H]];
    specialize (H t0) as [H _]; apply H in Et; contradiction H0; constructor; assumption.
Qed.

(* Everything after this requires an induction hypothesis, so let's just dive in *)

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
