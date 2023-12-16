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

Fixpoint typecheck (ctx : context) (t : term) : option (term * context) :=
  match t with
  | TmVarS x => match ctx with [] => None | (s, t) :: tl => if eqb x s then Some (t, tl) else None end
  | TmAtom id lvl => Some (TmAtom id (S lvl), ctx)
  (* | TmAtom id lvl => match ctx with [] => Some (TmAtom id (S lvl), ctx) | _ :: _ => None end *)
  | TmPack id arg ty curry =>
      let ectx := match arg with None => ctx | Some s => (s, ty) :: ctx end in
      match atom_id curry with
      | None => None
      | Some aid =>
          if eqb id aid then
            match typecheck ectx curry with
            | None => None
            | Some (ct, etc) => Some (TmForA arg ty ct, etc)
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

(* NOTE: THIS WILL EVENTUALLY NOT HOLD (when `Typed` is not unique)! *)
Theorem typed_implies_typecheck : forall ctx t ty,
  Typed ctx t ty ->
  typecheck ctx t = Some (ty, []).
Proof.
  intros. induction H.
  - simpl. rewrite eqb_refl. reflexivity.
  - reflexivity.
  - simpl. apply reflect_atom_id in H0. rewrite H0. rewrite eqb_refl. rewrite IHTyped. reflexivity.
  - simpl. apply reflect_atom_id in H0. rewrite H0. rewrite eqb_refl. rewrite IHTyped. reflexivity.
  - simpl. rewrite IHTyped. reflexivity.
  - simpl. rewrite IHTyped. reflexivity.
  - simpl. subst. eapply typecheck_weakening in IHTyped1. rewrite IHTyped1.
    simpl in *. rewrite IHTyped2. rewrite eq_term_refl. reflexivity.
  - simpl. subst. eapply typecheck_weakening in IHTyped1. rewrite IHTyped1.
    simpl in *. rewrite IHTyped2. rewrite eq_term_refl.
    apply reflect_subst in H2. rewrite H2. reflexivity.
Qed.

Theorem typed_unique : forall ctx t ty1 ty2,
  Typed ctx t ty1 ->
  Typed ctx t ty2 ->
  ty1 = ty2.
Proof.
  intros. apply typed_implies_typecheck in H. apply typed_implies_typecheck in H0.
  rewrite H0 in H. invert H. reflexivity.
Qed.

(*
Theorem typecheck_preserves_scope : forall ctx t ty ctx',
  typecheck ctx t = Some (ty, ctx') ->
  exists used, ctx = used ++ ctx'.
Proof.
  intros ctx t. generalize dependent ctx. induction t; intros; try discriminate.
  - simpl in *. destruct ctx; try discriminate H. destruct p.
    destruct (eqb id s); invert H. exists [(s, ty)]. reflexivity.
  - invert H. exists []. reflexivity.
  - destruct (atom_id t2); try discriminate H.
    destruct (eqb id s) eqn:Ee; try discriminate H. apply eqb_eq in Ee. subst.
    destruct arg.
    + destruct (typecheck ((s0, t1) :: ctx) t2) eqn:Et; try discriminate H. destruct p. invert H.
      apply IHt2 in Et. destruct Et. destruct x.
      * simpl in *. invert H. invert H0.
Qed.

Theorem typecheck_implies_typed : forall ctx t ty,
  typecheck ctx t = Some (ty, []) ->
  Typed ctx t ty.
Proof.
  intros ctx t. generalize dependent ctx. induction t; intros; simpl in *; try discriminate.
  - destruct ctx; try discriminate H. destruct p.
    destruct (eqb id s) eqn:E; invert H. apply eqb_eq in E. subst. constructor.
  - invert H. constructor.
  - destruct (atom_id t2) eqn:Ea; try discriminate H. apply reflect_atom_id in Ea.
    destruct (eqb id s) eqn:E; try discriminate H. apply eqb_eq in E. subst.
    destruct arg; [destruct (typecheck ((s0, t1) :: ctx) t2) eqn:Et | destruct (typecheck ctx t2) eqn:Et];
    try discriminate H; destruct p; invert H; apply IHt2 in Et; constructor; assumption.
  - destruct arg; [destruct (typecheck ((s, t1) :: ctx) t2) eqn:Et | destruct (typecheck ctx t2) eqn:Et];
    try discriminate H; destruct p; invert H; apply IHt2 in Et; constructor; assumption.
  - destruct (typecheck ctx t1) eqn:Et1; try discriminate H. destruct p. destruct t; try discriminate H.
    destruct (typecheck c t2) eqn:Et2; try discriminate H. destruct p.
    destruct (eq_term t3 t) eqn:Ee; try discriminate H. apply reflect_eq_term in Ee. subst.
    destruct arg; [destruct (subst s t2 t4) eqn:Es; try discriminate H; apply reflect_subst in Es |]; invert H.
    + apply IHt2 in Et2. eapply TyApplSome; [| apply Et2 | | apply Es].
Qed.

(* Extremely crucial theorem! *)
Theorem typecheck_correct : forall ctx t ty,
  (exists etc, typecheck ctx t = Some (ty, etc)) <-> Typed ctx t ty.
Proof.
  split; intros.
  - admit.
  - induction H; intros; try reflexivity.
    + simpl. rewrite eqb_refl. exists []. reflexivity.
    + exists []. reflexivity.
    + simpl.

    + simpl. rewrite eqb_refl. reflexivity.
    + simpl. apply reflect_atom_id in H0. rewrite H0. rewrite eqb_refl. rewrite IHTyped. reflexivity.
    + simpl. apply reflect_atom_id in H0. rewrite H0. rewrite eqb_refl. rewrite IHTyped. reflexivity.
    + simpl. rewrite IHTyped. reflexivity.
    + simpl. rewrite IHTyped. reflexivity.
    + simpl in *. generalize dependent body. generalize dependent ctx. generalize dependent f.
      generalize dependent x. generalize dependent ty. generalize dependent ctxb. induction ctxa.
      * intros. destruct ctxb; subst; simpl;
        rewrite IHTyped1; rewrite IHTyped2; rewrite eq_term_refl; reflexivity.
      * intros. subst. simpl in *. specialize (IHctxa ctxb ty x H0 IHTyped2). clear IHctxa.
Qed.

Theorem reflect_not_typecheck : forall ctx t,
  typecheck ctx t = None <-> ~exists ty, Typed ctx t ty.
Proof.
  split; intros.
Qed.
*)
