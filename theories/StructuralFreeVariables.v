From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  Invert
  Terms.

Fixpoint remove_all x li :=
  match li with
  | [] => []
  | hd :: tl =>
      let recursed := remove_all x tl in
      if eqb x hd then recursed else hd :: recursed
  end.
(* tail-recursive version flips the order *)

Theorem in_remove_all : forall x li,
  ~In x (remove_all x li).
Proof.
  intros x li C. generalize dependent x. induction li; intros; simpl in *. { destruct C. }
  destruct (eqb_spec x a). { apply IHli in C as []. } destruct C. { subst. apply n. reflexivity. } apply IHli in H as [].
Qed.

Theorem in_remove_all_neq : forall x y li,
  x <> y ->
  (In x (remove_all y li) <-> In x li).
Proof.
  intros x y li H. generalize dependent x. generalize dependent y. induction li; intros; simpl in *. { split; intros []. }
  destruct (eqb_spec y a).
  - subst. split; intros.
    + right. eapply IHli. { apply H. } assumption.
    + destruct H0. { subst. contradiction H. reflexivity. } apply IHli; assumption.
  - split; intros H0; (destruct H0; [left; assumption |]; right; eapply IHli; [apply H | assumption]).
Qed.

Fixpoint structural_fv t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmAppl f x =>
      structural_fv f ++ structural_fv x
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      structural_fv ty ++ (
        let recursed := structural_fv curry in
        match arg with
        | None => recursed
        | Some a => remove_all a recursed
        end)
  end.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv (TmForA (Some x) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_permits_interrupted_shadowing : forall x y, y <> x ->
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv (TmForA (Some x) TmVoid (TmForA (Some y) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  structural_fv (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

(*
Fixpoint structural_fv_fast acc t :=
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
      structural_fv_fast (structural_fv_fast acc b) a
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      structural_fv_fast (remove_if_head arg (structural_fv_fast acc curry)) ty
  end.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_fast_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv_fast [] (TmForA (Some x) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_fast_permits_interrupted_shadowing : forall x y, y <> x ->
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv_fast [] (TmForA (Some x) TmVoid (TmForA (Some y) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. rewrite H. rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_fast_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  structural_fv_fast [] (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. Abort.

Theorem structural_fv_fast_slow_eq : forall t,
  structural_fv_slow t = rev (snd (structural_fv_fast [] [] t)).
Proof.
  intros t. induction t; intros; simpl in *; try reflexivity.
  - destruct arg.
    + destruct (structural_fv_slow t2).
      * rewrite app_nil_r. rewrite IHt1. destruct (structural_fv_fast [] [] t1).
Qed.

Definition structural_fv := structural_fv_fast [].
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

Inductive StructurallyFreeIn : term -> list string -> Prop :=
  | FreeVoid :
      StructurallyFreeIn TmVoid []
  | FreeStar : forall univ,
      StructurallyFreeIn (TmStar univ) []
  | FreeAtom : forall id,
      StructurallyFreeIn (TmAtom id) []
  | FreeVarS : forall x,
      StructurallyFreeIn (TmVarS x) [x]
  | FreePack : forall id arg ty curry v,
      StructurallyFreeIn (TmForA    arg ty curry) v ->
      StructurallyFreeIn (TmPack id arg ty curry) v
  | FreeForA : forall arg ty curry va vb avb v,
      StructurallyFreeIn ty va ->
      StructurallyFreeIn curry avb ->
      (match arg with None => eq | Some a => Wherever a end) vb avb ->
      v = va ++ vb ->
      StructurallyFreeIn (TmForA arg ty curry) v
  | FreeAppl : forall f x va vb v,
      StructurallyFreeIn f va ->
      StructurallyFreeIn x vb ->
      va ++ vb = v ->
      StructurallyFreeIn (TmAppl f x) v
  .
Arguments StructurallyFreeIn t vs.

Definition ClosedStructural := fun t => StructurallyFreeIn t [].
Arguments ClosedStructural t/.

Lemma map_distr : forall {A B} (f : A -> B) hd tl, map f (hd ++ tl) = map f hd ++ map f tl.
Proof.
  intros. generalize dependent tl. generalize dependent B.
  induction hd; intros; simpl in *; try rewrite IHhd; reflexivity.
Qed.

Theorem reflect_structural_fv : forall t v,
  structural_fv t = v <-> StructurallyFreeIn t v.
Proof.
  split; intros.
  - generalize dependent v. induction t; intros; subst; simpl in *; try constructor;
    econstructor; try apply IHt1; try apply IHt2; try reflexivity;
    (destruct arg; [| reflexivity]); apply wherever_remove_all; reflexivity.
  - induction H; subst; simpl in *; try reflexivity. destruct arg; [| subst; reflexivity].
    apply wherever_remove_all in H1. subst. reflexivity.
Qed.
