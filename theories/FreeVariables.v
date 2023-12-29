From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  Invert
  OptionBind
  Partition
  Snoc
  Terms.

Fixpoint remove_all x li :=
  match li with
  | [] => []
  | hd :: tl =>
      let recursed := remove_all x tl in
      if eqb x hd then recursed else hd :: recursed
  end.
(* tail-recursive version flips the order *)

Definition remove_if_head x li :=
  match li with
  | [] => []
  | hd :: tl => if eqb x hd then tl else li
  end.
Arguments remove_if_head x/ li.

Fixpoint fv_with rm t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmAppl f x =>
      fv_with rm f ++ fv_with rm x
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      let lo := (
        let recursed := fv_with rm curry in
        match arg with
        | None => recursed
        | Some a => rm a recursed
        end) in
      partition_pf eqb (fv_with remove_all (* <-- yes, hard-code this *) ty) lo ++ lo
  end.
Definition fv := fv_with remove_if_head.
Arguments fv/ t.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv (TmForA (Some x) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_permits_interrupted_shadowing : forall x y, y <> x ->
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv (TmForA (Some x) TmVoid (TmForA (Some y) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. rewrite H. rewrite eqb_refl. reflexivity. Qed.

Example fv_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

(*
Fixpoint fv_fast acc t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      acc
  | TmVarS s =>
      s :: acc
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      fv_fast (fv_fast acc b) a
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      fv_fast (remove_if_head arg (fv_fast acc curry)) ty
  end.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_fast_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv_fast [] (TmForA (Some x) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_fast_permits_interrupted_shadowing : forall x y, y <> x ->
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv_fast [] (TmForA (Some x) TmVoid (TmForA (Some y) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. rewrite H. rewrite eqb_refl. reflexivity. Qed.

Example fv_fast_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv_fast [] (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. Abort.

Theorem fv_fast_slow_eq : forall t,
  fv_slow t = rev (snd (fv_fast [] [] t)).
Proof.
  intros t. induction t; intros; simpl in *; try reflexivity.
  - destruct arg.
    + destruct (fv_slow t2).
      * rewrite app_nil_r. rewrite IHt1. destruct (fv_fast [] [] t1).
Qed.

Definition fv := fv_fast [].
*)

Inductive Wherever {T} (x : T) : list T -> list T -> Prop :=
  | WhereverNil :
      Wherever x [] []
  | WhereverHere : forall a b,
      Wherever x a b ->
      Wherever x a (x :: b)
  | WhereverSkip : forall hd tla tlb,
      x <> hd ->
      Wherever x tla tlb ->
      Wherever x (hd :: tla) (hd :: tlb)
  .

Example wherever_12345 : Wherever 9 [1;2;3;4;5] [9;1;9;9;2;3;9;4;9;9;9;9;5;9].
Proof. repeat constructor; intro C; discriminate C. Qed.

Lemma wherever_refl : forall {T} (x : T) li,
  (~In x li) ->
  Wherever x li li.
Proof.
  induction li; constructor; apply Decidable.not_or in H as [H I]. { symmetry. assumption. } apply IHli. assumption.
Qed.

Lemma wherever_not_in_orig : forall {T} (x : T) li post,
  Wherever x li post ->
  ~In x li.
Proof.
  intros T x li post H C. generalize dependent C. generalize dependent post. generalize dependent x.
  induction li; intros; destruct C; subst.
  - remember (x :: li) as xli eqn:Ex. induction H; intros.
    { discriminate. } { apply IHWherever. assumption. } invert Ex. apply H. reflexivity.
  - remember (a :: li) as ali eqn:Ea. generalize dependent a. generalize dependent li. induction H; intros.
    { discriminate. } { eapply IHWherever. { apply IHli. } { assumption. } apply Ea. }
    invert Ea. eapply IHli. { apply H0. } assumption.
Qed.

Lemma wherever_remove_all : forall x li post,
  Wherever x li post <-> remove_all x post = li.
Proof.
  split; intros.
  - induction H.
    + reflexivity.
    + simpl. rewrite eqb_refl. assumption.
    + simpl. apply eqb_neq in H. rewrite H. f_equal. assumption.
  - generalize dependent x. generalize dependent li. induction post; intros.
    + invert H. constructor.
    + simpl in H. destruct (eqb x a) eqn:E.
      * apply eqb_eq in E. subst. constructor. apply IHpost. reflexivity.
      * apply eqb_neq in E. subst. constructor. { assumption. } apply IHpost. reflexivity.
Qed.

Variant MaybeCons {T} (hd : T) : list T -> list T -> Prop :=
  | MaybeConsNil :
      MaybeCons hd [] []
  | MaybeConsCons : forall tl,
      MaybeCons hd tl (hd :: tl)
  | MaybeConsNotEq : forall x etc,
      hd <> x ->
      MaybeCons hd (x :: etc) (x :: etc)
  .

Inductive FreeInWith : (string -> list string -> list string -> Prop) -> term -> list string -> Prop :=
  | FreeVoid : forall cmp,
      FreeInWith cmp TmVoid []
  | FreeStar : forall cmp univ,
      FreeInWith cmp (TmStar univ) []
  | FreeAtom : forall cmp id,
      FreeInWith cmp (TmAtom id) []
  | FreeVarS : forall cmp x,
      FreeInWith cmp (TmVarS x) [x]
  | FreePack : forall cmp id arg ty curry va vb avb v pf,
      FreeInWith Wherever ty va ->
      FreeInWith cmp curry avb ->
      Partition pf va vb ->
      v = pf ++ vb ->
      (match arg with None => eq | Some a => cmp a end) vb avb ->
      FreeInWith cmp (TmPack id arg ty curry) v
  | FreeForA : forall cmp arg ty curry va vb avb v pf,
      FreeInWith Wherever ty va ->
      FreeInWith cmp curry avb ->
      Partition pf va vb ->
      v = pf ++ vb ->
      (match arg with None => eq | Some a => cmp a end) vb avb ->
      FreeInWith cmp (TmForA arg ty curry) v
  | FreeAppl : forall cmp f x va vb v,
      FreeInWith cmp f va ->
      FreeInWith cmp x vb ->
      va ++ vb = v ->
      FreeInWith cmp (TmAppl f x) v
  .
Definition FreeIn := FreeInWith MaybeCons.
Arguments FreeIn/ t vs.

Definition Closed := fun t => FreeIn t [].
Arguments Closed t/.

Lemma map_distr : forall {A B} (f : A -> B) hd tl, map f (hd ++ tl) = map f hd ++ map f tl.
Proof.
  intros. generalize dependent tl. generalize dependent B.
  induction hd; intros; simpl in *; try rewrite IHhd; reflexivity.
Qed.

Theorem slow_down : forall {T} f hi lo,
  rev' (@partition_pf_fast T [] f hi lo) = partition_pf_slow f hi lo.
Proof. intros. rewrite <- partition_pf_fast_slow. reflexivity. Qed.

Theorem reflect_fv_structural : forall t v,
  fv_with remove_all t = v <-> FreeInWith Wherever t v.
Proof.
  split; intros.
  - generalize dependent v. induction t; intros; subst; simpl in *; repeat rewrite slow_down; try solve [constructor];
    [| | econstructor; [apply IHt1 | apply IHt2 |]; reflexivity];
    destruct arg; (econstructor; [apply IHt1 | apply IHt2 | | |]);
    try reflexivity; try apply wherever_remove_all; try reflexivity;
    rewrite <- partition_pf_fast_slow; apply partition_pf_works; apply eqb_spec.
  - remember Wherever as cmp eqn:Ec. generalize dependent Ec.
    induction H; intros; subst; simpl in *; try reflexivity; repeat rewrite slow_down;
    specialize (IHFreeInWith1 eq_refl); specialize (IHFreeInWith2 eq_refl); subst; [| | reflexivity];
    destruct arg; repeat rewrite wherever_remove_all in *; subst; f_equal;
    rewrite <- partition_pf_fast_slow; apply (reflect_partition_pf _ _ _ _ eqb_spec); assumption.
Qed.

Theorem reflect_fv : forall Cmp cmp t v,
  (forall a b z, Cmp a z b <-> cmp a b = z) ->
  (fv_with cmp t = v <-> FreeInWith Cmp t v).
Proof.
  split; intros.
  - generalize dependent Cmp. generalize dependent cmp. generalize dependent v.
    induction t; intros; subst; simpl in *; repeat rewrite slow_down; try solve [constructor];
    [| | econstructor; [apply (IHt1 _ _ eq_refl _ H) | apply (IHt2 _ _ eq_refl _ H) | reflexivity]];
    destruct arg; (econstructor; [apply reflect_fv_structural; reflexivity | apply (IHt2 _ _ eq_refl _ H) | | reflexivity |]);
    try apply H; try reflexivity; rewrite <- partition_pf_fast_slow; apply partition_pf_works; apply eqb_spec.
  - generalize dependent cmp.
    induction H0; intros; subst; simpl in *; try reflexivity; repeat rewrite slow_down;
    [| | rewrite (IHFreeInWith1 _ H0); rewrite (IHFreeInWith2 _ H0); reflexivity];
    (destruct arg; [apply H2 in H1 |]); subst; simpl in *; (rewrite IHFreeInWith2; [f_equal | assumption]);
    rewrite <- partition_pf_fast_slow; apply (reflect_partition_pf _ _ _ _ eqb_spec);
    (rewrite IHFreeInWith1; [assumption |]); intros; apply wherever_remove_all.
Qed.
