From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  StructuralFreeVariables
  Invert
  Partition
  Terms.

Definition remove_if_head x li :=
  match li with
  | [] => []
  | hd :: tl => if eqb x hd then tl else li
  end.
Arguments remove_if_head x/ li.

Fixpoint fv t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmAppl f x =>
      fv f ++ fv x
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      let lo := (
        let recursed := fv curry in
        match arg with
        | None => recursed
        | Some a => remove_if_head a recursed
        end) in
      partition_pf eqb (structural_fv ty) lo ++ lo
  end.

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

Variant MaybeCons {T} (hd : T) : list T -> list T -> Prop :=
  | MaybeConsNil :
      MaybeCons hd [] []
  | MaybeConsCons : forall tl,
      MaybeCons hd tl (hd :: tl)
  | MaybeConsNotEq : forall x etc,
      hd <> x ->
      MaybeCons hd (x :: etc) (x :: etc)
  .

Lemma maybe_cons_remove_if_head : forall x li post,
  MaybeCons x li post <-> remove_if_head x post = li.
Proof.
  split; intros.
  - invert H; simpl in *.
    + reflexivity.
    + rewrite eqb_refl. reflexivity.
    + apply eqb_neq in H0. rewrite H0. reflexivity.
  - destruct post; simpl in *.
    + subst. constructor.
    + destruct (eqb_spec x s); subst; constructor. assumption.
Qed.

Inductive FreeIn : term -> list string -> Prop :=
  | FreeVoid :
      FreeIn TmVoid []
  | FreeStar : forall univ,
      FreeIn (TmStar univ) []
  | FreeAtom : forall id,
      FreeIn (TmAtom id) []
  | FreeVarS : forall x,
      FreeIn (TmVarS x) [x]
  | FreePack : forall id arg ty curry v,
      FreeIn (TmForA    arg ty curry) v ->
      FreeIn (TmPack id arg ty curry) v
  | FreeForA : forall arg ty curry va vb avb v pf,
      StructurallyFreeIn ty va ->
      FreeIn curry avb ->
      Partition pf va vb ->
      v = pf ++ vb ->
      (match arg with None => eq | Some a => MaybeCons a end) vb avb ->
      FreeIn (TmForA arg ty curry) v
  | FreeAppl : forall f x va vb v,
      FreeIn f va ->
      FreeIn x vb ->
      va ++ vb = v ->
      FreeIn (TmAppl f x) v
  .
Arguments FreeIn t vs.

Definition Closed := fun t => FreeIn t [].
Arguments Closed t/.

Theorem slow_down : forall {T} f hi lo,
  rev' (@partition_pf_fast T [] f hi lo) = partition_pf_slow f hi lo.
Proof. intros. rewrite <- partition_pf_fast_slow. reflexivity. Qed.

Theorem reflect_fv : forall t v,
  (fv t = v <-> FreeIn t v).
Proof.
  split; intros.
  - generalize dependent v. induction t; intros; subst; simpl in *; try solve [constructor]; [constructor | |];
    econstructor; try apply reflect_structural_fv; try apply IHt1; try apply IHt2; try reflexivity;
    try apply (partition_pf_works _ _ _ eqb_spec); (destruct arg; [apply maybe_cons_remove_if_head |]); reflexivity.
  - induction H; subst; simpl in *; try reflexivity. eapply (reflect_partition_pf _ _ _ _ eqb_spec) in H1.
    apply reflect_structural_fv in H. destruct arg; [apply maybe_cons_remove_if_head in H3 |]; subst; reflexivity.
Qed.
