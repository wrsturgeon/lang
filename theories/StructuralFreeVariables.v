From Coq Require Export
  Lists.List.
Export ListNotations.
From Lang Require Import
  InTactics
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

Lemma in_remove_all : forall x li,
  ~In x (remove_all x li).
Proof.
  intros x li C. generalize dependent x. induction li; intros; simpl in *. { destruct C. }
  destruct (eqb_spec x a). { apply IHli in C as []. } destruct C. { subst. apply n. reflexivity. } apply IHli in H as [].
Qed.

Lemma in_remove_all_neq : forall x y li,
  x <> y ->
  (In x (remove_all y li) <-> In x li).
Proof.
  intros x y li H. generalize dependent x. generalize dependent y. induction li; intros; simpl in *. { split; intros []. }
  destruct (eqb_spec y a).
  - subst. split; intros.
    + right. eapply IHli; eassumption.
    + destruct H0. { subst. contradiction H. reflexivity. } apply IHli; assumption.
  - split; intros H0; (destruct H0; [left; assumption |]; right; eapply IHli; eassumption).
Qed.

Lemma remove_all_app : forall x a b,
  remove_all x (a ++ b) = remove_all x a ++ remove_all x b.
Proof.
  intros x a. generalize dependent x. induction a; intros; simpl in *. { reflexivity. }
  destruct (eqb_spec x a). { apply IHa. } simpl. f_equal. apply IHa.
Qed.

Lemma rev_remove_all : forall x li,
  rev (remove_all x li) = remove_all x (rev li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  rewrite remove_all_app. simpl. destruct (eqb x a). { rewrite app_nil_r. apply IHli. } simpl. f_equal. apply IHli.
Qed.

Lemma remove_all_swap : forall x y li,
  remove_all x (remove_all y li) = remove_all y (remove_all x li).
Proof.
  intros. generalize dependent x. generalize dependent y. induction li; intros; simpl in *. { reflexivity. }
  destruct (eqb_spec y a). { subst. destruct (eqb_spec x a). { subst. reflexivity. } simpl. rewrite eqb_refl. apply IHli. }
  destruct (eqb_spec x a). { subst. simpl. rewrite eqb_refl. apply IHli. }
  simpl. apply eqb_neq in n. apply eqb_neq in n0. rewrite n. rewrite n0. f_equal. apply IHli.
Qed.

Lemma remove_all_shadow : forall x li,
  remove_all x (remove_all x li) = remove_all x li.
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct (eqb x a) eqn:E. { apply IHli. } simpl. rewrite E. f_equal. apply IHli.
Qed.

Fixpoint structural_fv_slow t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [s]
  | TmAppl f x =>
      structural_fv_slow f ++ structural_fv_slow x
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      structural_fv_slow ty ++ (
        let recursed := structural_fv_slow curry in
        match arg with
        | None => recursed
        | Some a => remove_all a recursed
        end)
  end.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_slow_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv_slow (
    TmForA (Some x) TmVoid (
      TmForA (Some x) TmVoid (
        TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_slow_permits_interrupted_shadowing : forall x y,
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv_slow (
    TmForA (Some x) TmVoid (
      TmForA (Some y) TmVoid (
        TmForA (Some x) TmVoid (
          TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  structural_fv_slow (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

Fixpoint structural_fv_fast acc shadowed t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      acc
  | TmVarS s =>
      if existsb (eqb s) shadowed then acc else s :: acc
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      structural_fv_fast (structural_fv_fast acc shadowed a) shadowed b
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      structural_fv_fast (structural_fv_fast acc shadowed ty) (arg :: shadowed) curry
  end.

Definition structural_fv t := rev' (structural_fv_fast [] [] t).
Arguments structural_fv/ t.

(* Crucial distinction from an easier-to-implement algorithm! *)
Example structural_fv_fast_permits_shadowing : forall x,
  (* Equivalent to `\x. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv (
    TmForA (Some x) TmVoid (
      TmForA (Some x) TmVoid (
        TmAppl (TmVarS x) (TmVarS x)))) = [].
Proof. intros. simpl. repeat rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_fast_permits_interrupted_shadowing : forall x y,
  (* Equivalent to `\x. \y. \x. x x`, where the `x`s are distinct and pushed/popped in order. *)
  structural_fv (
    TmForA (Some x) TmVoid (
      TmForA (Some y) TmVoid (
        TmForA (Some x) TmVoid (
          TmAppl (TmVarS x) (TmVarS x))))) = [].
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example structural_fv_fast_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  structural_fv (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. reflexivity. Qed.

Lemma structural_fv_fast_acc : forall hd tl shadowed t,
  structural_fv_fast (hd ++ tl) shadowed t = structural_fv_fast hd shadowed t ++ tl.
Proof.
  intros. generalize dependent hd. generalize dependent tl. generalize dependent shadowed.
  induction t; intros; simpl in *; try reflexivity;
  [destruct (existsb (eqb id) shadowed); reflexivity | destruct arg | destruct arg |];
  rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

Lemma fold_left_rm_nil : forall shadowed,
  fold_left (fun li x => remove_all x li) shadowed [] = [].
Proof. induction shadowed. { reflexivity. } assumption. Qed.

Lemma fold_left_rm_app : forall a b rm,
  let f := fun li x => remove_all x li in
  fold_left f rm a ++ fold_left f rm b = fold_left f rm (a ++ b).
Proof.
  intros. unfold f. clear f. generalize dependent b. generalize dependent a.
  induction rm; intros; simpl in *. { reflexivity. } rewrite remove_all_app. apply IHrm.
Qed.

Lemma structural_fv_fast_shadowed : forall acc shadowed t,
  structural_fv_fast acc shadowed t = fold_left (fun li x => remove_all x li) shadowed (structural_fv_fast [] [] t) ++ acc.
Proof.
  intros. generalize dependent acc. generalize dependent shadowed.
  induction t; intros; simpl in *; try rewrite fold_left_rm_nil; try reflexivity.
  - destruct (existsb_in eqb id shadowed eqb_spec).
    + induction shadowed; destruct i; simpl; [subst; rewrite eqb_refl | destruct (eqb_spec a id)];
      try (rewrite fold_left_rm_nil; reflexivity). apply IHshadowed. assumption.
    + induction shadowed; simpl in *. { reflexivity. }
      apply Decidable.not_or in n as [Ha H]. apply eqb_neq in Ha. rewrite Ha. apply IHshadowed. assumption.
  - destruct arg; simpl in *; rewrite IHt1; rewrite IHt2; rewrite app_assoc; f_equal.
    + rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)). rewrite <- fold_left_rm_app. f_equal.
      rewrite (IHt2 [s]). simpl. rewrite app_nil_r. reflexivity.
    + rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)). apply fold_left_rm_app.
  - destruct arg; simpl in *; rewrite IHt1; rewrite IHt2; rewrite app_assoc; f_equal.
    + rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)). rewrite <- fold_left_rm_app. f_equal.
      rewrite (IHt2 [s]). simpl. rewrite app_nil_r. reflexivity.
    + rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)). apply fold_left_rm_app.
  - rewrite IHt1. rewrite IHt2. rewrite app_assoc. f_equal.
    rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)). apply fold_left_rm_app.
Qed.

Theorem structural_fv_fast_slow : forall t,
  structural_fv t = structural_fv_slow t.
Proof.
  intros. simpl in *. unfold rev'. rewrite <- rev_alt. induction t; intros; simpl in *; try reflexivity.
  - destruct arg; rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)); rewrite rev_app_distr; rewrite IHt1;
    [rewrite structural_fv_fast_shadowed; rewrite app_nil_r; simpl; rewrite rev_remove_all |]; rewrite IHt2; reflexivity.
  - destruct arg; rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)); rewrite rev_app_distr; rewrite IHt1;
    [rewrite structural_fv_fast_shadowed; rewrite app_nil_r; simpl; rewrite rev_remove_all |]; rewrite IHt2; reflexivity.
  - rewrite (structural_fv_fast_acc [] (structural_fv_fast [] [] t1)).
    rewrite rev_app_distr. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

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
  intros. rewrite structural_fv_fast_slow. split; intros.
  - generalize dependent v. induction t; intros; subst; simpl in *; try constructor;
    econstructor; try apply IHt1; try apply IHt2; try reflexivity;
    (destruct arg; [| reflexivity]); apply wherever_remove_all; reflexivity.
  - induction H; subst; simpl in *; try reflexivity. destruct arg; [| subst; reflexivity].
    apply wherever_remove_all in H1. subst. reflexivity.
Qed.
