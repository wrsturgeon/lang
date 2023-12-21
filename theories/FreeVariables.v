From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  Invert
  Mint
  OptionBind
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
Arguments remove_if_head/ x li.

Fixpoint fv_slow t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmAppl f x =>
      fv_slow f ++ fv_slow x
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      fv_slow ty ++ (
        let recursed := fv_slow curry in
        match arg with
        | None => recursed
        | Some a => (if mint ty then remove_all else remove_if_head) a recursed
        end)
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
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. reflexivity. Qed.

Example fv_slow_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv_slow (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

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
Proof. intros. apply eqb_neq in H. simpl. rewrite eqb_refl. reflexivity. Qed.

Example fv_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

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

Inductive FreeIn : term -> list string -> Prop :=
  | FreeVoid :
      FreeIn TmVoid []
  | FreeStar : forall univ,
      FreeIn (TmStar univ) []
  | FreeAtom : forall id,
      FreeIn (TmAtom id) []
  | FreeVarS : forall x,
      FreeIn (TmVarS x) [x]
  | FreePack : forall id arg ty curry va vb avb v,
      FreeIn ty va ->
      FreeIn curry avb ->
      va ++ vb = v ->
      (match arg with None => eq | Some a => if mint ty then Wherever a else MaybeCons a end) vb avb ->
      FreeIn (TmPack id arg ty curry) v
  | FreeForA : forall arg ty curry va vb avb v,
      FreeIn ty va ->
      FreeIn curry avb ->
      va ++ vb = v ->
      (match arg with None => eq | Some a => if mint ty then Wherever a else MaybeCons a end) vb avb ->
      FreeIn (TmForA arg ty curry) v
  | FreeAppl : forall f x va vb v,
      FreeIn f va ->
      FreeIn x vb ->
      va ++ vb = v ->
      FreeIn (TmAppl f x) v
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
  - induction H; intros; subst; simpl in *; f_equal;
    (destruct arg; [| symmetry; assumption]);
    (destruct (reflect_mint ty); [apply wherever_remove_all; assumption |]);
    (invert H2; [| rewrite eqb_refl | apply eqb_neq in H4; rewrite H4]); reflexivity.
  - generalize dependent v. induction t; intros; subst; simpl in *; try solve [constructor];
    econstructor; try apply IHt1; try apply IHt2; try reflexivity;
    (destruct arg; [| reflexivity]); (destruct (reflect_mint t1); [apply wherever_remove_all; reflexivity |]);
    (destruct (fv_slow t2); [constructor |]); (destruct (eqb s s0) eqn:E; [apply eqb_eq in E; subst |]); constructor;
    apply eqb_neq in E; assumption.
Qed.
