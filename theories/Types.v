From Coq Require Export
  Lists.List
  Sorting.Permutation.
Export ListNotations.
From Lang Require Import
  Closed
  Invert
  Subst
  Terms.

Definition context : Set := list (string * term).
Arguments context/.

Definition judgment : Type := context -> term -> term -> Prop.
Arguments judgment/.

Inductive WithWeakening (P : judgment) : judgment :=
  | WeakSkip : forall hd tl t t',
      WithWeakening P tl t t' ->
      WithWeakening P (hd :: tl) t t'
  | WeakOrig : forall ctx t t',
      P ctx t t' ->
      WithWeakening P ctx t t'
  .

Inductive WithContraction (P : judgment) : judgment :=
  | CntrCopy : forall hd tl t t',
      WithContraction P (hd :: hd :: tl) t t' ->
      WithContraction P (hd :: tl) t t'
  | CntrOrig : forall ctx t t',
      P ctx t t' ->
      WithContraction P ctx t t'
  .

Inductive WithExchange (P : judgment) : judgment :=
  | ExchPerm : forall ctx1 ctx2 t t',
      WithExchange P ctx2 t t' ->
      Permutation ctx1 ctx2 ->
      WithExchange P ctx1 t t'
  | ExchOrig : forall ctx t t',
      P ctx t t' ->
      WithExchange P ctx t t'
  .

(* Typed extremely strictly, as if on a stack: no exchange, no weakening, no contraction. *)
Inductive Typed : context -> term -> term -> Prop :=
  | TyVarS : forall id t,
      Typed [(id, t)] (TmVarS id) t
  | TyAtom : forall id,
      Typed [] (TmAtom id) (TmAtom id)
  | TyPack : forall ctx ctxt ctxc id arg ty curry t kind,
      Typed ctxt ty kind ->
      Typed (match arg with Some x => (x, ty) :: ctxc | None => ctxc end) curry t ->
      ctxt ++ ctxc = ctx ->
      AtomId id curry ->
      Typed ctx (TmPack id arg ty curry) (TmForA arg ty t)
  | TyForA : forall ctx ctxt ctxc arg ty body t kind,
      Typed ctxt ty kind ->
      Typed (match arg with Some x => (x, ty) :: ctxc | None => ctxc end) body t ->
      ctxt ++ ctxc = ctx ->
      Typed ctx (TmForA arg ty body) (TmForA arg ty t)
  | TyApplNone : forall ctx ctxf ctxx f x ty body,
      Typed ctxf f (TmForA None ty body) ->
      Typed ctxx x ty ->
      ctx = ctxf ++ ctxx ->
      Typed ctx (TmAppl f x) body
  | TyApplSome : forall ctx ctxf ctxx f x arg ty body sub,
      Typed ctxf f (TmForA (Some arg) ty body) ->
      Typed ctxx x ty ->
      ctx = ctxf ++ ctxx ->
      subst arg x body = Some sub ->
      Typed ctx (TmAppl f x) sub
  (*
  | TyStar : forall ctx t ty,
      Typed ctx t ty ->
      Typed ctx t TmStar
  *)
  .

(* TODO: CRUCIAL SAFETY THEOREMS: (1) Star does not have type Star, and (2) no term has type Void *)

(* Showing that, given f: X -> Y and x: X, we can type (f x) : Y. *)
Example type_fn_app :
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X Y) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fx := TmAppl f x in
  Typed ctx fx Y.
Proof. simpl. eapply TyApplNone. { apply TyVarS. } { apply TyVarS. } reflexivity. Qed.

(* Almost exactly like the above, but trying to use `x` twice (f : X -> X -> Y). Successfully rejected. *)
Example type_prevents_reuse : ~exists t,
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X (TmForA None X Y)) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fxx := TmAppl (TmAppl f x) x in
  Typed ctx fxx t.
Proof.
  (* In all cases, we have to use the concatenation hypothesis to show that we can't use `x` twice. *)
  intros [t C]. simpl in *.
  remember [
    ("f"%string, TmForA None (TmVarS "X") (TmForA None (TmVarS "X") (TmVarS "Y")));
    ("x"%string, TmVarS "X")] as ctx eqn:Ec. generalize dependent Ec.
  remember (TmAppl (TmAppl (TmVarS "f") (TmVarS "x")) (TmVarS "x")) as ty eqn:Et. generalize dependent Et.
  induction C; intros; simpl in *; subst; try discriminate;
  try (invert Et; invert C1; invert H1; invert Ec; destruct ctxx0; invert H3; destruct ctxx; invert H4; invert C2);
  try (invert Et; invert C1; invert H2; invert Ec);
  try (
    invert C; [| invert H1; invert H3; invert H4 | apply (IHC eq_refl eq_refl)];
    invert H1; invert H2; invert H5; destruct ctxx0; destruct ctxx; invert H3; invert H6; invert H4).
Qed.

(* ...But the above becomes perfectly okay if we add exchange and contraction, i.e., a heap: *)
Example type_contraction_allows_reuse :
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X (TmForA None X Y)) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fxx := TmAppl (TmAppl f x) x in
  WithExchange (WithContraction (WithExchange Typed)) ctx fxx Y.
Proof.
  simpl.
  eapply ExchPerm. apply ExchOrig. (* Move `x` to the front *)
  apply CntrCopy. apply CntrOrig. (* Copy it *)
  eapply ExchPerm. apply ExchOrig. (* Move both to the back again *)
  repeat econstructor. (* This does a LOT of work for us; now only permutations left *)
  - simpl. eapply perm_trans. { eapply perm_trans. { apply perm_skip. apply perm_swap. } apply perm_swap. }
    repeat apply perm_skip. apply perm_nil.
  - apply perm_swap.
Qed.

(* TODO: Maybe take an argument in `Typed` that represents the typing relation in hypotheses,
 * so we don't have to nest structural rules like above. *)

(* NOTE: If we can type all functions s.t. output type represents only actual possible outputs,
   then we should be able to prove that all arrow types have an input type size
   greater than or equal to its output type size!
   Dizzying implications in terms of what a program has to start with--TODO: figure this out.
   This might be a crucial lemma in proving type safety (since a void output implies void input)! *)

(* Fantastic that we can prove something this precise! *)
Theorem typed_free_in : forall ctx t ty,
  Typed ctx t ty -> FreeIn t (map fst ctx).
Proof.
  intros. induction H; intros; simpl in *; subst; repeat rewrite map_distr; try assumption;
  try destruct arg; econstructor; try apply IHTyped1; try apply IHTyped2; reflexivity.
Qed.

Theorem fv_not_typed : forall t,
  fv t <> [] -> ~exists ty, Typed [] t ty.
Proof.
  intros t H [ty C]. apply typed_free_in in C. apply reflect_fv in C.
  rewrite C in H. contradiction H. reflexivity.
Qed.

Theorem typed_fv : forall ctx t ty,
  Typed ctx t ty ->
  fv t = map fst ctx.
Proof. intros. apply reflect_fv. eapply typed_free_in. apply H. Qed.

(* Look up a value by key and remove it from a key-value list. *)
Fixpoint yoink {T} s (li : list (string * T)) :=
  match li with
  | [] => None
  | (k, v) :: tl => if eqb s k then Some (v, tl) else
      let f : (T * (list (string * T))) -> _ := fun x =>
        let (out, etc) := x in (out, (k, v) :: etc) in
      option_map f (yoink s tl)
  end.

Example yoink_12345 :
  yoink "c" [("a", 1); ("b", 2); ("c", 3); ("d", 4); ("e", 5)]%string =
  Some (3, [("a", 1); ("b", 2); ("d", 4); ("e", 5)]%string).
Proof. reflexivity. Qed.

Theorem yoink_app : forall {T} s a b out etc,
  @yoink T s (a ++ b) = Some (out, etc) ->
  ((exists pre, etc = pre ++ b /\ yoink s a = Some (out, pre)) \/
  (exists post, etc = a ++ post /\ yoink s a = None /\ yoink s b = Some (out, post))).
Proof.
  intros T s a. generalize dependent s. induction a; intros; simpl in *; subst.
  - right. eexists. repeat split; assumption.
  - destruct a. destruct (eqb s s0) eqn:E.
    + apply eqb_eq in E. invert H. left. eexists. repeat split.
    + destruct (yoink s (a0 ++ b)) eqn:Ey; try discriminate H. destruct p. invert H.
      apply IHa in Ey. destruct Ey as [[pre [H1 H2]] | [post [H1 [H2 H3]]]]; subst; simpl in *.
      * left. rewrite H2. eexists; repeat split; try reflexivity.
      * right. rewrite H2. rewrite H3. eexists; repeat split.
Qed.

Fixpoint yank {T} i (li : list T) :=
  match li with
  | [] => None
  | hd :: tl =>
      match i with
      | O => Some (hd, tl)
      | S j => 
          let f := fun x : _ * _ => let (out, etc) := x in (out, hd :: etc) in
          option_map f (yank j tl)
      end
  end.

Fixpoint checked_sub amt from :=
  match from, amt with
  | _, O => Some from
  | S f, S a => checked_sub a f
  | _, _ => None
  end.

Example checked_sub_3_5 : checked_sub 3 5 = Some 2. Proof. reflexivity. Qed.
Example checked_sub_5_3 : checked_sub 5 3 = None. Proof. reflexivity. Qed.

Theorem checked_sub_le : forall amt from,
  checked_sub amt from <> None <-> amt <= from.
Proof.
  induction amt; intros; simpl in *.
  - split; intros. { apply le_0_n. } intro C. destruct from; discriminate C.
  - split; intros; destruct from; try contradiction. { apply le_n_S. apply IHamt. assumption. }
    { invert H. } apply le_S_n in H. apply IHamt. assumption.
Qed.

Theorem checked_sub_sub : forall amt from out,
  checked_sub amt from = out ->
  from - amt = match out with Some x => x | None => O end.
Proof.
  induction amt; intros; simpl in *. { destruct from; invert H; reflexivity. }
  destruct from; subst; simpl in *. { reflexivity. } apply IHamt. reflexivity.
Qed.

Theorem yank_app : forall {T} i a b,
  @yank T i (a ++ b) =
  match checked_sub (Datatypes.length a) i with
  | None =>
      let f : _ * _ -> _ := fun x => let (out, etc) := x in (out, etc ++ b) in
      option_map f (yank i a)
  | Some past_a =>
      let f : _ * _ -> _ := fun x => let (out, etc) := x in (out, a ++ etc) in
      option_map f (yank past_a b)
  end.
Proof.
  intros T i a. generalize dependent i. induction a; intros; simpl in *.
  - destruct i; destruct b; simpl; try reflexivity.
    destruct (yank i b); simpl; try reflexivity. destruct p. reflexivity.
  - destruct i; simpl in *. { reflexivity. } rewrite IHa. clear IHa.
    destruct (checked_sub (Datatypes.length a0) i); simpl in *.
    + destruct (yank n b); simpl; try reflexivity. destruct p. reflexivity.
    + destruct (yank i a0); try reflexivity. destruct p. reflexivity.
Qed.

Lemma nth_error_short_circuit : forall {T} i a b out,
  @nth_error T a i = Some out ->
  nth_error (a ++ b) i = Some out.
Proof.
  intros T i a. generalize dependent i. induction a; intros; simpl in *. { destruct i; discriminate H. }
  destruct i; simpl in *. { invert H. reflexivity. } apply IHa. assumption.
Qed.

Lemma nth_error_smap : forall f li i,
  nth_error (smap f li) i = option_map (fun pair : _ * _ => let (a, b) := pair in (a, f b)) (nth_error li i).
Proof.
  intros f li. generalize dependent f. induction li; intros; simpl in *. { destruct i; reflexivity. }
  destruct a. destruct i; simpl in *. { reflexivity. } apply IHli.
Qed.

(*
Theorem grand_unified_subst_preserves_typing : forall ctx t ty,
  Typed ctx t ty ->
  forall i s st ctx',
  yank i ctx = Some ((s, st), ctx') ->
  exists f,
  nth_error (grand_unified_subst t) i = Some (s, f) /\
  forall y,
  Typed [] y st ->
  Typed ctx' (f y) ty.
Proof.
  intros ctx t ty H. induction H; intros; simpl in *; subst.
  - destruct i; [| destruct i; discriminate]. invert H. eexists. repeat split. intros. assumption.
  - destruct i; discriminate H.
  - rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:Ec;
    [destruct (yank n ctxc) eqn:Ey | destruct (yank i ctxt) eqn:Ey]; try discriminate H3; destruct p; invert H3.
    + admit.
    + destruct arg.
      * admit.
      * eapply IHTyped1 in Ey as [f [E1 E2]]. clear IHTyped1; clear IHTyped2.
        erewrite nth_error_short_circuit; [| rewrite nth_error_smap; rewrite E1; reflexivity].
        eexists; repeat split. intros. apply E2 in H1. simpl. eapply TyPack. Print Typed. econstructor. assumption.
        rewrite nth_error_smap. rewrite E1; reflexivity.

    + assert (A : checked_sub (Datatypes.length ctxt) i <> None). { rewrite Ec. intro C. discriminate C. }
      apply checked_sub_le in A. destruct arg.
      * rewrite nth_error_app2; rewrite smap_len; assert (F := typed_fv _ _ _ H);
        rewrite grand_unified_subst_exactly_fv in F; eassert (L := f_equal _ F);
        repeat rewrite map_length in L; rewrite L; try assumption.
        clear IHTyped1; clear IHTyped2. eexists. split.
        -- rewrite (checked_sub_sub _ _ _ Ec).
  - destruct arg.
    + clear IHTyped1; clear IHTyped2.

    + admit.
    + rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:Ec.
      * destruct (yank n ctxc) eqn:Ey; try discriminate H3. destruct p. destruct p. invert H3.
        apply IHTyped2 in Ey as [f [E1 E2]].
        assert (A : checked_sub (Datatypes.length ctxt) i <> None). { rewrite Ec. intro C. discriminate C. }
        apply checked_sub_le in A. eexists. rewrite nth_error_app2; [|
          rewrite smap_len; apply typed_fv in H; rewrite grand_unified_subst_exactly_fv in H;
          eapply f_equal in H; repeat rewrite map_length in H; rewrite H; assumption].
        split. admit. intros. simpl in *. clear IHTyped1; clear IHTyped2.

    + rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i). clear IHTyped1; clear IHTyped2.
  - rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:E.
    + destruct (yank n ctxc) eqn:Ey; try discriminate H3. clear IHTyped1; clear IHTyped2. destruct p. invert H3. destruct arg.
      * admit.
      * assert (A := checked_sub_le (Datatypes.length ctxt) i).
      * apply checked_sub_le in E. Search nth_error. simpl in *.

  - clear IHTyped1; clear IHTyped2. assert (A := typed_fv _ _ _ H). rewrite grand_unified_subst_exactly_fv in A. destruct arg.
    + admit.
    + 

  intros ctx. induction ctx; intros; simpl in *. { destruct i; discriminate H0. }
  Search fv.
  assert (A := typed_fv _ _ _ H).
  rewrite grand_unified_subst_exactly_fv in A.
  destruct a.
  apply grand_unified_subst_exactly_fv 
  Search grand_unified_subst.
  apply IHctx.
Qed.

Theorem grand_unified_subst_preserves_typing : forall ctx t ty,
  (* A mouthful: if you substitute a variable in context with something of its assigned type,
   * and if you then remove that variable from the context,
   * then the type of the whole expression after substitution doesn't change. *)
  Typed ctx t ty ->
  forall x xt ctx',
  yoink x ctx = Some (xt, ctx') ->
  forall y,
  Typed [] y xt ->
  exists s,
  subst x y t = Some s /\ Typed ctx' s ty.
Proof.
  intros ctx t ty H. induction H; intros; simpl in *; subst; try discriminate.
  - destruct (eqb x id) eqn:E; invert H. apply eqb_eq in E. subst. simpl in *.
    eexists. split. { reflexivity. } assumption.
  - apply yoink_app in H3. destruct H3 as [[pre [E1 E2]] | [post [E1 [E2 E3]]]].
    + eapply IHTyped1 in E2 as [s [E2 E3]]. clear IHTyped1; clear IHTyped2. subst. destruct arg.
    + clear IHTyped1; clear IHTyped2. simpl in *.
Qed.

Theorem subst_preserves_typing : forall x y t ty s,
  Typed [] t ty ->
  subst x y t = Some s ->
  Typed [] s ty.
Proof.
  intros x y t. generalize dependent y. generalize dependent x.
  induction t; intros; simpl in *; try discriminate.
  - apply typed_fv in H. discriminate H.
  - invert H. destruct ctxt; destruct ctxc; invert H9. clear H0. destruct arg.
    + admit.
    + eapply IHt2.

  - assert (A := fv_not_typed (TmVarS id)). contradiction A. { intro C. discriminate C. } exists ty. assumption.
  - clear H0. induction H.
    + eapply IHt2.
  - destruct arg.
    + clear H0. invert H. simpl in *.

  - destruct (eqb x id) eqn:E; invert H0. apply eqb_eq in E. subst. induction H.
Qed.
*)
