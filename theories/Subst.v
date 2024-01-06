From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  FreeVariables
  Invert
  Partition
  StructuralFreeVariables
  StructuralHole
  StructuralSubst
  Terms.

Fixpoint checked_sub this_much from :=
  match this_much with
  | O => Some from
  | S n =>
      match from with
      | O => None
      | S m => checked_sub n m
      end
  end.

Example checked_sub_3_5 : checked_sub 3 5 = Some 2. Proof. reflexivity. Qed.
Example checked_sub_5_3 : checked_sub 5 3 = None. Proof. reflexivity. Qed.

Fixpoint subst_hole_acc acc x t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      (SHoleTerm t, match acc with None => None | Some _ => Some O end)
  | TmVarS z =>
      if eqb z x then
        match acc with
        (* no shadowing *)
        | Some O => (SHoleHere, None)
        (* shadowed *)
        | Some (S n) => (SHoleTerm t, Some 1)
        (* already used *)
        | None => (SHoleTerm t, None)
        end
      else
        (SHoleTerm t, match acc with None => None | Some _ => Some O end)
  | TmPack id arg ty curry =>
      let shadow := if eq_opt arg (Some x) then option_map S acc else acc in
      let (scurry, ac1) := subst_hole_acc shadow x curry in
      (SHolePack id arg (match acc with Some O => structural_subst_hole x ty | _ => SHoleTerm ty end) scurry, ac1)
  | TmForA arg ty body =>
      let shadow := if eq_opt arg (Some x) then option_map S acc else acc in
      let (sbody, ac1) := subst_hole_acc shadow x body in
      (SHoleForA arg (match acc with Some O => structural_subst_hole x ty | _ => SHoleTerm ty end) sbody, ac1)
  | TmAppl f z =>
      let (sf, tmp) := subst_hole_acc acc x f in
      (* `tmp` represents the number of shadowed instances that `f` consumed *)
      let acc' := match tmp with None => None | Some n => match acc with None => None | Some m => checked_sub n m end end in
      let (sz, out) := subst_hole_acc acc' x z in
      (SHoleAppl sf sz, out)
  end.
Definition subst_hole := subst_hole_acc (Some O).
Arguments subst_hole/ x t.
Definition subst x y t := sfill (fst (subst_hole x t)) y.
Arguments subst/ x y t.

Example subst_simple_f : forall f x y, (* note that we don't require `f <> x` *)
  (* subst f y (f x) = y x *)
  subst f y (TmAppl (TmVarS f) (TmVarS x)) = TmAppl y (TmVarS x).
Proof. intros. simpl. rewrite eqb_refl. destruct (eqb x f); reflexivity. Qed.

Example subst_simple_x : forall f x y, f <> x ->
  (* subst x y (f x) = f y *)
  subst x y (TmAppl (TmVarS f) (TmVarS x)) = TmAppl (TmVarS f) y.
Proof. intros. simpl. apply eqb_neq in H. rewrite H. rewrite eqb_refl. simpl. reflexivity. Qed.

Example subst_lambda_t : forall t x y, x <> t ->
  (* subst t y (\x:t. x x) = \x:y. x x *)
  subst t y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) y (TmAppl (TmVarS x) (TmVarS x)).
Proof. intros. simpl. apply eqb_neq in H. rewrite H. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example subst_lambda_x : forall t x y, t <> x ->
  (* subst x y (\x:t. x x) = \x:t. x y *)
  subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) y). (* Note that we ignore the first `x`! *)
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example subst_lambda_x_l : forall t x y, t <> x ->
  subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) (TmVarS x)) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) y) (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example subst_lambda_x_r : forall t x y, t <> x ->
  subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl (TmVarS x) (TmVarS x)))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl y (TmVarS x))).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example subst_scope : forall x y,
  (* In which `(\x. 0) x` should not let the bound `x` escape its scope and capture the second (free) `x`. *)
  subst x y (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = (TmAppl (TmForA (Some x) TmVoid TmVoid) y).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example subst_arg_cant_be_its_own_type : forall x y,
  subst x y (TmForA (Some x) (TmVarS x) TmVoid) = (TmForA (Some x) y TmVoid).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example subst_many_times_in_types : forall x y,
  subst x y (TmForA None (TmVarS x) (TmForA None (TmVarS x) TmVoid)) = (TmForA None y (TmForA None y TmVoid)).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example subst_type_shadowing : forall x y,
  subst x y (TmForA (Some x) (TmVarS x) (TmForA None (TmVarS x) TmVoid)) = (TmForA (Some x) y (TmForA None (TmVarS x) TmVoid)).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Theorem remove_all_partition_pf : forall x hi lo,
  remove_all x (partition_pf eqb hi lo) = partition_pf eqb (remove_all x hi) (remove_all x lo).
Proof.
  intros. repeat rewrite partition_pf_fast_slow. generalize dependent x. generalize dependent lo.
  induction hi; intros; simpl in *. { reflexivity. }
  destruct (existsb (eqb a) lo) eqn:El; simpl. {
    rewrite IHhi. destruct (eqb_spec x a). { reflexivity. } simpl.
    rewrite existsb_remove_all_neq; [| intro C; subst; apply n; reflexivity]. rewrite El. reflexivity. }
  destruct (existsb (eqb a) hi) eqn:Eh; simpl. {
    rewrite IHhi. destruct (eqb_spec x a). { reflexivity. } simpl.
    repeat (rewrite existsb_remove_all_neq; [| intro C; subst; apply n; reflexivity]). rewrite El. rewrite Eh. reflexivity. }
  destruct (eqb_spec x a). { apply IHhi. } simpl.
  repeat (rewrite existsb_remove_all_neq; [| intro C; subst; apply n; reflexivity]).
  rewrite El. rewrite Eh. simpl. f_equal. apply IHhi.
Qed.

Inductive TryRemove {T} (x : T) : list T -> list T -> Prop :=
  | TryRemoveNil :
      TryRemove x [] []
  | TryRemoveEq : forall tl,
      TryRemove x (x :: tl) tl
  | TryRemoveNeq : forall hd tl tl',
      x <> hd ->
      TryRemove x tl tl' ->
      TryRemove x (hd :: tl) (hd :: tl')
  .

Lemma try_remove_xor : forall {T} x pre post,
  @TryRemove T x pre post ->
  ((In x pre /\ pre <> post) \/ (~In x pre /\ pre = post)).
Proof.
  intros. induction H; simpl in *.
  - right. split. { intros []. } reflexivity.
  - left. split. { left. reflexivity. } intro C. induction tl. { discriminate C. } invert C. apply IHtl in H1 as [].
  - destruct IHTryRemove as [[IH1 IH2] | [IH1 IH2]].
    + left. split. { right. assumption. } intro C. invert C. apply IH2. reflexivity.
    + right. split. { intros [C | C]. { subst. apply H. reflexivity. } apply IH1 in C as []. } f_equal. assumption.
Qed.

(*
Theorem subst_fv : forall x y t,
  Closed y ->
  StructurallyClosed y -> (* this is clunky but `Closed y -> StructurallyClosed y` is either insanely difficult or false *)
  TryRemove x (fv t) (fv (subst x y t)).
Proof.
  intros x y t Hf Hs. simpl in *. generalize dependent x. generalize dependent y.
  induction t; intros; simpl in *; try solve [repeat constructor]; repeat rewrite slow_down in *.
  - destruct (eqb_spec id x); [subst; apply reflect_fv in Hf; simpl; rewrite Hf |]; repeat constructor.
    intro C. subst. apply n. reflexivity.
  - specialize (IHt1 _ Hf Hs). specialize (IHt2 _ Hf Hs).
    destruct (subst_hole_acc (if eq_opt arg (Some x) then Some 1 else Some 0) x t2) as [scurry ac1] eqn:Es.
    simpl in *. rewrite slow_down. destruct arg as [arg |]; simpl in *.
    + admit.
    + assert (A := IHt2 x). rewrite Es in A. simpl in A. induction A.

      assert (X := A). apply try_remove_xor in X as [[X1 X2] | [X1 X2]].
      * admit.
      * rewrite <- X2. 

  - specialize (IHt1 _ Hf Hs). specialize (IHt2 _ Hf Hs).
    destruct (subst_hole_acc (if eq_opt arg (Some x) then Some 1 else Some 0) x t2) as [scurry ac1] eqn:E.
    simpl. rewrite slow_down. destruct arg as [arg |]; simpl in *; rewrite remove_all_app;
    repeat rewrite <- partition_pf_fast_slow; rewrite remove_all_partition_pf; repeat rewrite partition_pf_fast_slow. 2: {
      assert (A := IHt2 x). rewrite E in A. simpl in A. rewrite A. f_equal. f_equal. apply structural_subst_fv. assumption. }
    destruct (eqb_spec arg x). 2: { assert (A := IHt2 x). rewrite E in A. simpl in A. rewrite A.
      destruct (fv t2) eqn:Ef2; simpl. { f_equal. f_equal. apply structural_subst_fv. assumption. }
      destruct (eqb_spec x s); subst; simpl in *. {
        rewrite eqb_refl in A. apply eqb_neq in n. rewrite n. simpl. rewrite eqb_refl.
        destruct (remove_all s l); simpl. { f_equal. f_equal. apply structural_subst_fv. assumption. }
        destruct (eqb_spec arg s0).
Qed.

Fixpoint count_slow {T} (f : T -> bool) li :=
  match li with
  | [] => O
  | hd :: tl => let n := count_slow f tl in if f hd then S n else n
  end.

Fixpoint count_fast acc {T} (f : T -> bool) li :=
  match li with
  | [] => acc
  | hd :: tl => count_fast (if f hd then S acc else acc) f tl
  end.
Definition count := @count_fast O.
Arguments count/ {T} f li.

Lemma count_fast_acc : forall acc {T} f li,
  count_fast (S acc) f li = S (@count_fast acc T f li).
Proof.
  intros. generalize dependent acc. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. } destruct (f a); apply IHli.
Qed.

Theorem count_fast_slow : forall {T} f li,
  count f li = @count_slow T f li.
Proof.
  intros. generalize dependent f. induction li; intros; simpl in *. { reflexivity. }
  destruct (f a); [rewrite count_fast_acc; f_equal |]; apply IHli.
Qed.

Theorem subst_fv : forall t x y n,
  count (eqb x) (fv t) = S n ->
  count (eqb x) (fv (subst x y t)) = n + count (eqb x) (fv y).
Proof.
  intros. simpl in *. repeat rewrite count_fast_slow in *. generalize dependent x. generalize dependent y.
  generalize dependent n. induction t; intros; try discriminate H.
  - simpl in *. destruct (eqb_spec x id); invert H. rewrite eqb_refl. reflexivity.
  - simpl in *. destruct (subst_hole_acc (if eq_opt arg (Some x) then Some 1 else Some O) x t2) as [scurry ac1] eqn:E.
    simpl in *. rewrite slow_down in *. destruct arg; simpl in *.
    + admit.
    + Print partition_pf_slow. 
Qed.

Lemma remove_key_if_head_incl : forall {T} x (li : list (string * T)),
  incl (remove_key_if_head x li) li.
Proof.
  unfold incl. intros T x [] [a1 a2] H. { inversion H. } destruct p. simpl in H. destruct (eqb x s); [right |]; assumption.
Qed.

Theorem incl_partition_pf_fst : forall {T} hi lo,
  incl (@partition_pf_slow (string * T) fst_cmp hi lo) hi.
Proof.
  unfold incl. induction hi; intros; simpl in *. { destruct H. }
  destruct (existsb (fst_cmp a) lo) eqn:El; simpl in *. { right. apply (IHhi _ _ H). }
  destruct (existsb (fst_cmp a) hi) eqn:Eh; simpl in *. { right. apply (IHhi _ _ H). }
  destruct a as [k1 v1]. destruct a0 as [k2 v2]. destruct H; [| right; apply (IHhi _ _ H)].
  left. assumption.
Qed.
*)

Lemma subst_id_deconstructed : forall acc x t,
  sfill (fst (subst_hole_acc acc x t)) (TmVarS x) = t.
Proof.
  intros. generalize dependent acc. generalize dependent x. induction t; intros; simpl in *; try reflexivity.
  - destruct (eqb_spec id x); [subst |]; destruct acc; [destruct n | | |]; reflexivity.
  - destruct (subst_hole_acc (if eq_opt arg (Some x) then option_map S acc else acc) x t2) as [scurry ac1] eqn:E.
    simpl in *. f_equal. { destruct acc; [destruct n |]; try reflexivity. apply structural_subst_id. }
    assert (A := IHt2 x (if eq_opt arg (Some x) then option_map S acc else acc)). rewrite E in A. simpl in A. assumption.
  - destruct (subst_hole_acc (if eq_opt arg (Some x) then option_map S acc else acc) x t2) as [scurry ac1] eqn:E.
    simpl in *. f_equal. { destruct acc; [destruct n |]; try reflexivity. apply structural_subst_id. }
    assert (A := IHt2 x (if eq_opt arg (Some x) then option_map S acc else acc)). rewrite E in A. simpl in A. assumption.
  - destruct (subst_hole_acc acc x t1) as [sf tmp] eqn:E1. destruct tmp; [destruct acc |];
    [destruct (subst_hole_acc (checked_sub n n0) x t2) as [sz out] eqn:E2 | |];
    try destruct (subst_hole_acc None x t2) as [sz out] eqn:E2; simpl in *;
    eassert (A1 := IHt1 _ _); eassert (A2 := IHt2 _ _); rewrite E1 in A1; rewrite E2 in A2;
    simpl in *; rewrite A1; rewrite A2; reflexivity.
Qed.

Theorem subst_id : forall x t,
  subst x (TmVarS x) t = t.
Proof. apply subst_id_deconstructed. Qed.

(* TODO: `Prop` versions
Definition Subst (x : string) (y t t' : term) := exists h, SubstHole x t h /\ Fill h y t'.
Arguments Subst/ x y t t'.
*)
