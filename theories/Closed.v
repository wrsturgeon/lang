From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  Invert
  OptionBind
  Snoc
  Terms.

Fixpoint destructive_search needle haystack :=
  match haystack with
  | [] => None
  | hd :: tl => if eqb needle hd then Some tl else destructive_search needle tl
  end.

Fixpoint fv_slow t :=
  match t with
  | TmVoid
  | TmStar
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      fv_slow a ++ fv_slow b
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      fv_slow ty ++
      match fv_slow curry with
      | [] => []
      | hd :: tl => if eqb arg hd then tl else hd :: tl
      end
  end.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_slow_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv_slow (TmForA (Some x) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example fv_slow_permits_interrupted_shadowing : forall x y, y <> x ->
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  fv_slow (TmForA (Some x) TmVoid (TmForA (Some y) TmVoid (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. rewrite H. rewrite eqb_refl. reflexivity. Qed.

Example fv_slow_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv_slow (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

Fixpoint fv_fast acc t :=
  match t with
  | TmVoid
  | TmStar
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
      let tmp := match fv_fast acc curry with
      | [] => []
      | hd :: tl => if eqb arg hd then tl else hd :: tl
      end in
      fv_fast tmp ty
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

(*
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

Definition fv := fv_slow.
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

Inductive FreeIn : term -> list string -> Prop :=
  | FreeVoid :
      FreeIn TmVoid []
  | FreeStar :
      FreeIn TmStar []
  | FreeAtom : forall id,
      FreeIn (TmAtom id) []
  | FreeVarS : forall x,
      FreeIn (TmVarS x) [x]
  | FreePackNone : forall id ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      FreeIn (TmPack id None ty curry) v
  | FreeForANone : forall ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      FreeIn (TmForA None ty curry) v
  | FreeAppl : forall f x va vb v,
      FreeIn f va ->
      FreeIn x vb ->
      va ++ vb = v ->
      FreeIn (TmAppl f x) v
  | FreePackMatch : forall id arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry (arg :: vb) ->
      va ++ vb = v ->
      FreeIn (TmPack id (Some arg) ty curry) v
  | FreeForAMatch : forall arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry (arg :: vb) ->
      va ++ vb = v ->
      FreeIn (TmForA (Some arg) ty curry) v
  | FreePackDiff : forall id arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      hd_error vb <> Some arg ->
      FreeIn (TmPack id (Some arg) ty curry) v
  | FreeForADiff : forall arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      hd_error vb <> Some arg ->
      FreeIn (TmForA (Some arg) ty curry) v
  .

Definition Closed := fun t => FreeIn t [].
Arguments Closed t/.

Lemma map_distr : forall {A B} (f : A -> B) hd tl, map f (hd ++ tl) = map f hd ++ map f tl.
Proof.
  intros. generalize dependent tl. generalize dependent B.
  induction hd; intros; simpl in *; try rewrite IHhd; reflexivity.
Qed.

Theorem reflect_fv : forall t v,
  FreeIn t v <-> fv t = v.
Proof.
  split; intros.
  - induction H; intros; simpl in *; subst; try rewrite IHFreeIn2; try rewrite eqb_refl; try reflexivity;
    destruct (fv_slow curry); try reflexivity; destruct (eqb arg s) eqn:E; try reflexivity;
    rewrite eqb_eq in E; subst; contradiction H2; reflexivity.
  - generalize dependent v. induction t; intros; simpl in *; subst; try solve [econstructor].
    + destruct arg; try (econstructor; try apply IHt1; try apply IHt2; reflexivity). destruct (fv_slow t2).
      { eapply FreePackDiff; try apply IHt1; try apply IHt2; try reflexivity. intro C. discriminate C. }
      destruct (eqb s s0) eqn:E.
      * apply eqb_eq in E. subst. econstructor; try apply IHt1; try apply IHt2; reflexivity.
      * apply eqb_neq in E. eapply FreePackDiff; try apply IHt1; try apply IHt2; try reflexivity.
        intro C. simpl in C. invert C. contradiction E. reflexivity.
    + destruct arg; try (econstructor; try apply IHt1; try apply IHt2; reflexivity). destruct (fv_slow t2).
      { eapply FreeForADiff; try apply IHt1; try apply IHt2; try reflexivity. intro C. discriminate C. }
      destruct (eqb s s0) eqn:E.
      * apply eqb_eq in E. subst. econstructor; try apply IHt1; try apply IHt2; reflexivity.
      * apply eqb_neq in E. eapply FreeForADiff; try apply IHt1; try apply IHt2; try reflexivity.
        intro C. simpl in C. invert C. contradiction E. reflexivity.
    + econstructor; try apply IHt1; try apply IHt2; reflexivity.
Qed.

Fixpoint str_in li s :=
  match li with
  | [] => false
  | hd :: tl => if eqb s hd then true else str_in tl s
  end.
