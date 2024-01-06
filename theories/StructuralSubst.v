From Coq Require Export
  List.
Export ListNotations.
From Coq Require Import
  Ascii.
From Lang Require Import
  FstCmp
  InTactics
  Invert
  NonEmpty
  StructuralHole
  StructuralFreeVariables
  Terms.

Fixpoint smap {A B}
  (f : B -> B)
  (x : list (A * B)) :
  list (A * B) :=
  match x with
  | [] => []
  | (s, g) :: tl => (s, f g) :: smap f tl
  end.

Theorem smap_distr : forall {A B} f a b,
  @smap A B f (a ++ b) = smap f a ++ smap f b.
Proof.
  intros A B f a. generalize dependent f. induction a; intros; simpl in *.
  { reflexivity. } destruct a. rewrite IHa. reflexivity.
Qed.

Theorem smap_len : forall {A B} f li,
  Datatypes.length (@smap A B f li) = Datatypes.length li.
Proof.
  intros A B f li. generalize dependent f. induction li; intros; simpl in *.
  { reflexivity. } destruct a. simpl. rewrite IHli. reflexivity.
Qed.

Theorem map_fst_smap : forall {A B} f li,
  map fst (@smap A B f li) = map fst li.
Proof. induction li. { reflexivity. } destruct a. simpl. rewrite IHli. reflexivity. Qed.

Fixpoint remove_key_all {T} x (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, f) :: tl =>
      let recursed := remove_key_all x tl in
      if eqb x s then recursed else (s, f) :: recursed
  end.

Lemma remove_all_key_eq : forall {T} x (li : list (string * T)),
  map fst (remove_key_all x li) = remove_all x (map fst li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. destruct (eqb x s) eqn:E. { apply IHli. } simpl. f_equal. apply IHli.
Qed.

Lemma remove_key_all_eq : forall {T} x li,
  ~In x (map fst li) ->
  @remove_key_all T x li = li.
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl in *. apply Decidable.not_or in H as [H1 H2]. apply eqb_neq in H1.
  rewrite eqb_sym in H1. rewrite H1. f_equal. apply IHli. assumption.
Qed.

Fixpoint fold_rm_acc {A B} out (pred : A -> bool) (f : A -> B -> B) acc li :=
  match li with
  | [] => (acc, out)
  | hd :: tl =>
      if pred hd then
        fold_rm_acc out pred f (f hd acc) tl
      else
        fold_rm_acc (hd :: out) pred f acc tl
  end.
Definition fold_rm {A B} := @fold_rm_acc A B [].
Arguments fold_rm {A B}/ pred f acc li.

Fixpoint structural_subst_hole x t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      SHoleTerm t
  | TmVarS z =>
      if eqb z x then SHoleHere else SHoleTerm t
  | TmPack id arg ty curry =>
      SHolePack id arg (structural_subst_hole x ty) (
        if eq_opt arg (Some x) then
          SHoleTerm curry
        else
          structural_subst_hole x curry)
  | TmForA arg ty body =>
      SHoleForA arg (structural_subst_hole x ty) (
        if eq_opt arg (Some x) then
          SHoleTerm body
        else
          structural_subst_hole x body)
  | TmAppl f z =>
      SHoleAppl (structural_subst_hole x f) (structural_subst_hole x z)
  end.
Definition structural_subst x y t := sfill (structural_subst_hole x t) y.
Arguments structural_subst/ x y t.

Example structural_subst_simple_f : forall f x y, x <> f ->
  (* subst f y (f x) = y x *)
  structural_subst f y (TmAppl (TmVarS f) (TmVarS x)) = TmAppl y (TmVarS x).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example structural_subst_simple_x : forall f x y, f <> x ->
  (* subst x y (f x) = f y *)
  structural_subst x y (TmAppl (TmVarS f) (TmVarS x)) = TmAppl (TmVarS f) y.
Proof. intros. simpl. apply eqb_neq in H. rewrite H. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_lambda_t : forall t x y, x <> t ->
  (* subst t y (\x:t. x x) = \x:y. x x *)
  structural_subst t y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) y (TmAppl (TmVarS x) (TmVarS x)).
Proof. intros. simpl. apply eqb_neq in H. rewrite H. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_lambda_x : forall t x y, t <> x ->
  (* subst x y (\x:t. x x) = \x:t. x x, UNLIKE the non-structural version (in which only the first `x` is substituted *)
  structural_subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example structural_subst_lambda_x_l : forall t x y, t <> x ->
  (* subst x y (\x:t. ((x x) x) = \x:t. ((x x) x), again UNLIKE the non-structural version *)
  structural_subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) (TmVarS x)) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) (TmVarS x)) (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example structural_subst_lambda_x_r : forall t x y, t <> x ->
  structural_subst x y (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl (TmVarS x) (TmVarS x)))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl (TmVarS x) (TmVarS x))).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. simpl. reflexivity. Qed.

Example structural_subst_scope : forall x y,
  (* In which `(\x. 0) x` should not let the bound `x` escape its scope and capture the second (free) `x`. *)
  structural_subst x y (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = (TmAppl (TmForA (Some x) TmVoid TmVoid) y).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_arg_cant_be_its_own_type : forall x y,
  structural_subst x y (TmForA (Some x) (TmVarS x) TmVoid) = (TmForA (Some x) y TmVoid).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_many_times_in_types : forall x y,
  structural_subst x y (TmForA None (TmVarS x) (TmForA None (TmVarS x) TmVoid)) = (TmForA None y (TmForA None y TmVoid)).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_type_shadowing : forall x y,
  structural_subst x y (TmForA (Some x) (TmVarS x) (TmForA None (TmVarS x) TmVoid)) = (TmForA (Some x) y (TmForA None (TmVarS x) TmVoid)).
Proof. intros. simpl. rewrite eqb_refl. simpl. reflexivity. Qed.

Example structural_subst_simple : forall f repl x, x <> f ->
  structural_subst f repl (TmAppl (TmVarS f) (TmVarS x)) = (TmAppl repl (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. reflexivity. Qed.

Example structural_subst_shadowing : forall x y,
  structural_subst x y (TmForA (Some x) TmVoid (TmVarS x)) = TmForA (Some x) TmVoid (TmVarS x). (* unchanged *)
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example structural_subst_not_shadowing : forall x y z, z <> x ->
  structural_subst x y (TmForA (Some z) TmVoid (TmVarS x)) = TmForA (Some z) TmVoid y. (* changed *)
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma fst_cmp_eqb : forall {T} a a' b b',
  @fst_cmp T T (a, b) (a', b') = eqb a a'.
Proof. reflexivity. Qed.

Theorem Forall_smap : forall {A B} f P li,
  Forall (fun p : A * B => let (x, g) := p in P (x, f g)) li ->
  Forall P (smap f li).
Proof.
  intros. remember (fun p : _ * _ => let (x, g) := p in P (x, f g)) as F eqn:EF.
  generalize dependent P. generalize dependent f. induction H; intros; [apply Forall_nil |].
  destruct x as [s g]. subst. simpl in *. constructor; [assumption |]. apply IHForall. reflexivity.
Qed.

Lemma remove_key_all_incl : forall {T} x (li : list (string * T)),
  incl (remove_key_all x li) li.
Proof.
  unfold incl. intros T x li. generalize dependent x. induction li; intros; simpl in *. { destruct H. }
  destruct a. destruct (eqb x s) eqn:E. { apply eqb_eq in E. subst. right. eapply IHli. apply H. }
  destruct a0. destruct H. { left. assumption. } right. eapply IHli. apply H.
Qed.

(* God this is the dumbest function of all time but it's only ever used in proofs *)
Fixpoint slow_unique_key {T} (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, t) :: tl => (s, t) :: remove_key_all s (slow_unique_key tl)
  end.

Lemma has_remove_key_all : forall {T} (x y : string * T) (li : list (string * T)),
  fst_cmp x y = false ->
  existsb (fst_cmp x) (remove_key_all (fst y) li) = existsb (fst_cmp x) li.
Proof.
  intros. generalize dependent y. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. destruct x. destruct y. unfold fst_cmp in *. simpl in *.
  destruct (eqb s1 s) eqn:E1. { apply eqb_eq in E1. subst. rewrite H. apply (IHli (s0, t0) (s, t)). assumption. }
  destruct (eqb s0 s) eqn:E0; simpl in *. { rewrite E0. reflexivity. } rewrite E0. apply (IHli (s0, t0) (s1, t1)). assumption.
Qed.

Lemma has_slow_unique : forall {T} x li,
  existsb (@fst_cmp T T x) (slow_unique_key li) = existsb (fst_cmp x) li.
Proof.
  intros T [s t] li. generalize dependent t. generalize dependent s.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. destruct (eqb_spec s s0). { subst. unfold fst_cmp. simpl. rewrite eqb_refl. reflexivity. }
  simpl. rewrite (has_remove_key_all (s, t) (s0, t0)). 2: { unfold fst_cmp. simpl. apply eqb_neq. assumption. }
  unfold fst_cmp. simpl. apply eqb_neq in n. rewrite n. apply (IHli _ t).
Qed.

Theorem structural_subst_id : forall x t,
  structural_subst x (TmVarS x) t = t.
Proof.
  intros. generalize dependent x. induction t; intros; simpl in *; try reflexivity.
  - destruct (eqb_spec id x); subst; reflexivity.
  - destruct (eq_opt_spec arg (Some x)); subst; simpl in *; rewrite IHt1; [| rewrite IHt2]; reflexivity.
  - destruct (eq_opt_spec arg (Some x)); subst; simpl in *; rewrite IHt1; [| rewrite IHt2]; reflexivity.
  - rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Theorem not_in_structural_subst_fv : forall x y t,
  ~In x (structural_fv y) ->
  ~In x (structural_fv (structural_subst x y t)).
Proof.
  intros. rewrite structural_fv_fast_slow in *. generalize dependent x. generalize dependent y.
  induction t; intros; simpl in *; intro C; try solve [destruct C];
  [destruct (eqb_spec id x); subst; simpl in *;
    [apply H in C as [] |]; destruct C; [| destruct H0]; apply n; assumption | | |];
  specialize (IHt1 _ _ H); specialize (IHt2 _ _ H); try destruct arg; apply in_app_iff in C as [C | C];
  try apply IHt1 in C as []; try apply IHt2 in C as []; simpl in *;
  (destruct (eqb_spec s x); [subst; eapply in_remove_all; apply C |]);
  (apply in_remove_all_neq in C; [| intro E; subst; apply n; reflexivity]); apply IHt2 in C as [].
Qed.

Inductive StructuralSubstHole (x : string) : term -> structural_hole -> Prop :=
  | SSubstVoid :
      StructuralSubstHole x TmVoid (SHoleTerm TmVoid)
  | SSubstStar : forall univ,
      StructuralSubstHole x (TmStar univ) (SHoleTerm (TmStar univ))
  | SSubstVarSEq :
      StructuralSubstHole x (TmVarS x) SHoleHere
  | SSubstVarSNEq : forall y,
      x <> y ->
      StructuralSubstHole x (TmVarS y) (SHoleTerm (TmVarS y))
  | SSubstAtom : forall id,
      StructuralSubstHole x (TmAtom id) (SHoleTerm (TmAtom id))
  | SSubstPackShadow : forall id ty curry ty',
      StructuralSubstHole x ty ty' ->
      StructuralSubstHole x (TmPack id (Some x) ty curry) (SHolePack id (Some x) ty' (SHoleTerm curry))
  | SSubstPack : forall id arg ty curry ty' curry',
      arg <> Some x ->
      StructuralSubstHole x ty ty' ->
      StructuralSubstHole x curry curry' ->
      StructuralSubstHole x (TmPack id arg ty curry) (SHolePack id arg ty' curry')
  | SSubstForAShadow : forall ty body ty',
      StructuralSubstHole x ty ty' ->
      StructuralSubstHole x (TmForA (Some x) ty body) (SHoleForA (Some x) ty' (SHoleTerm body))
  | SSubstForA : forall arg ty body ty' body',
      arg <> Some x ->
      StructuralSubstHole x ty ty' ->
      StructuralSubstHole x body body' ->
      StructuralSubstHole x (TmForA arg ty body) (SHoleForA arg ty' body')
  | SSubstAppl : forall f z f' z',
      StructuralSubstHole x f f' ->
      StructuralSubstHole x z z' ->
      StructuralSubstHole x (TmAppl f z) (SHoleAppl f' z')
  .
Definition StructuralSubst (x : string) (y t t' : term) := exists h, StructuralSubstHole x t h /\ StructuralFill h y t'.
Arguments StructuralSubst/ x y t t'.

Theorem reflect_structural_subst_hole : forall x t h,
  structural_subst_hole x t = h <-> StructuralSubstHole x t h.
Proof.
  split; intros.
  - generalize dependent x. generalize dependent h. induction t; intros; subst; simpl in *; try solve [constructor].
    + destruct (eqb_spec id x). { subst. constructor. } constructor. intro C. subst. apply n. reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. constructor. apply IHt1. reflexivity. }
      constructor; [assumption | apply IHt1 | apply IHt2]; reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. constructor. apply IHt1. reflexivity. }
      constructor; [assumption | apply IHt1 | apply IHt2]; reflexivity.
    + constructor; [apply IHt1 | apply IHt2]; reflexivity.
  - induction H; simpl in *; try rewrite eqb_refl; try rewrite IHStructuralSubstHole;
    try rewrite IHStructuralSubstHole1; try rewrite IHStructuralSubstHole2; try reflexivity.
    + apply eqb_neq in H. rewrite eqb_sym in H. rewrite H. reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. contradiction H. reflexivity. } reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. contradiction H. reflexivity. } reflexivity.
Qed.

Theorem reflect_structural_subst : forall x y t t',
  structural_subst x y t = t' <-> StructuralSubst x y t t'.
Proof.
  simpl in *. split; intros.
  - generalize dependent x. generalize dependent y. generalize dependent t'.
    induction t; intros; subst; simpl in *; try solve [repeat econstructor];
    [destruct (eqb_spec id x); [subst |]; simpl; repeat econstructor; intro C; subst; apply n; reflexivity | | |];
    specialize (IHt1 _ y x eq_refl) as [h1 [IHh1 IHf1]];
    specialize (IHt2 _ y x eq_refl) as [h2 [IHh2 IHf2]];
    [| | eexists; split; constructor; eassumption];
    (destruct (eq_opt_spec arg (Some x)); [subst; simpl |]);
    eexists; split; constructor; try eassumption; constructor.
  - destruct H as [h [Hh Hf]]. generalize dependent y. generalize dependent t'.
    induction Hh; intros; invert Hf; simpl in *; try rewrite eqb_refl; simpl in *; try reflexivity;
    try (destruct (eq_opt_spec arg (Some x)); [subst; contradiction H; reflexivity |]);
    try (f_equal; [apply IHHh1 | apply IHHh2]; assumption).
    + apply eqb_neq in H. rewrite eqb_sym in H. rewrite H. reflexivity.
    + invert H6. f_equal. apply IHHh. assumption.
    + invert H5. f_equal. apply IHHh. assumption.
Qed.

Theorem structural_subst_not_in : forall x y t f,
  StructurallyFreeIn t f ->
  ~In x f ->
  StructuralSubst x y t t.
Proof.
  intros. generalize dependent x. generalize dependent y. generalize dependent f.
  induction t; intros; simpl in *; invert H; try solve [eexists; split; constructor]; [| invert H6 | |];
  try (rewrite in_app_iff in H0; apply Decidable.not_or in H0 as [Hva Hvb]);
  try (specialize (IHt1 _ H3 y _ Hva) as [h1 [H1h H1f]]; specialize (IHt2 _ H4));
  [| | specialize (IHt1 _ H4 y _ Hva) as [h1 [H1h H1f]]; specialize (IHt2 _ H5) |]; try (
    destruct arg as [arg |]; [apply wherever_remove_all in H7 |]; subst;
    [destruct (eqb_spec x arg); [subst | rewrite in_remove_all_neq in Hvb; [| assumption]] |];
    try specialize (IHt2 y _ Hvb) as [h2 [H2h H2f]]; eexists; split; constructor; try eassumption;
    [constructor | |]; intro C; invert C; apply n; reflexivity).
  - eexists. split. { constructor. intro C. subst. apply H0. left. reflexivity. } constructor.
  - specialize (IHt2 y _ Hvb) as [h2 [H2h H2f]]. eexists. split; constructor; eassumption.
Qed.

(* doesn't make sense with non-structural holes, so it's okay to drop the `structural_` *)
Fixpoint closed_hole h :=
  match h with
  | SHoleHere => false
  | SHoleTerm _ => true
  | SHolePack _ _ ty curry => andb (closed_hole ty) (closed_hole curry)
  | SHoleForA _ ty body => andb (closed_hole ty) (closed_hole body)
  | SHoleAppl f x => andb (closed_hole f) (closed_hole x)
  end.

Inductive ClosedHole : structural_hole -> Prop :=
  | ClosedHoleTerm : forall t,
      ClosedHole (SHoleTerm t)
  | ClosedHolePack : forall id arg ty curry,
      ClosedHole ty ->
      ClosedHole curry ->
      ClosedHole (SHolePack id arg ty curry)
  | ClosedHoleForA : forall arg ty body,
      ClosedHole ty ->
      ClosedHole body ->
      ClosedHole (SHoleForA arg ty body)
  | ClosedHoleAppl : forall f x,
      ClosedHole f ->
      ClosedHole x ->
      ClosedHole (SHoleAppl f x)
  .

Theorem reflect_closed_here : forall h,
  Bool.reflect (ClosedHole h) (closed_hole h).
Proof.
  induction h; simpl in *.
  - constructor. intro C. invert C.
  - constructor. constructor.
  - invert IHh1. 2: { constructor. intro C. invert C. apply H0 in H3 as []. }
    invert IHh2; constructor. { constructor; assumption. } intro C. invert C. apply H2 in H8 as [].
  - invert IHh1. 2: { constructor. intro C. invert C. apply H0 in H3 as []. }
    invert IHh2; constructor. { constructor; assumption. } intro C. invert C. apply H2 in H7 as [].
  - invert IHh1. 2: { constructor. intro C. invert C. apply H0 in H3 as []. }
    invert IHh2; constructor. { constructor; assumption. } intro C. invert C. apply H2 in H6 as [].
Qed.

Theorem closed_iff_identity : forall h,
  ClosedHole h <-> forall x y, sfill h x = sfill h y.
Proof.
  split.
  - intro H. induction H; intros; simpl in *; try rename x into x0;
    try rewrite (IHClosedHole1 x0 y); try rewrite (IHClosedHole2 x0 y); try reflexivity.
  - induction h; intros; simpl in *; try constructor; try apply IHh1; try apply IHh2;
    try (intros; specialize (H x y); invert H; reflexivity). specialize (H TmVoid (TmStar O)). discriminate H.
Qed.

(* This doesn't work, since substituting a non-closed term might capture a lambda argument. *)
(*
Theorem structural_subst_fv : forall x y t,
  structural_fv (structural_subst x y t) =
  ne_intersp
    (fun hd => app (hd ++ structural_fv y))
    (splitrm (eqb x) (structural_fv t)).
Proof.
  intros. rewrite splitrm_fast_slow. generalize dependent x. generalize dependent y.
  induction t; intros; simpl in *; try reflexivity.
  - destruct (eqb_spec id x). { subst. rewrite eqb_refl. simpl. rewrite app_nil_r. reflexivity. }
    apply eqb_neq in n. rewrite eqb_sym in n. rewrite n. reflexivity.
  - rewrite IHt1. destruct arg as [arg |]; simpl in *.
    + rewrite <- ne_intersp_splitrm. f_equal. destruct (eqb_spec arg x); simpl in *.
      * subst. rewrite splitrm_remove_all. reflexivity.
      * shelve.
    + rewrite IHt2. apply ne_intersp_splitrm.
    Unshelve. rewrite splitrm_remove_all_neq; [| intro C; subst; apply n; reflexivity]. rewrite IHt2. Abort.
*)

Theorem structural_subst_closed : forall x y t,
  StructurallyClosed y ->
  structural_fv (structural_subst x y t) = remove_all x (structural_fv t).
Proof.
  intros. repeat rewrite structural_fv_fast_slow. simpl in *. generalize dependent x. generalize dependent y.
  induction t; intros; simpl in *; try reflexivity.
  - destruct (eqb_spec id x).
    + subst. rewrite eqb_refl. simpl. rewrite <- structural_fv_fast_slow. apply reflect_structural_fv. assumption.
    + apply eqb_neq in n. rewrite eqb_sym in n. rewrite n. reflexivity.
  - specialize (IHt1 _ H). specialize (IHt2 _ H). rewrite IHt1.
    destruct arg as [arg |]; simpl in *; rewrite remove_all_app; f_equal; [| apply IHt2].
    destruct (eqb_spec arg x). { subst. symmetry. apply remove_all_shadow. } rewrite remove_all_swap. f_equal. apply IHt2.
  - specialize (IHt1 _ H). specialize (IHt2 _ H). rewrite IHt1.
    destruct arg as [arg |]; simpl in *; rewrite remove_all_app; f_equal; [| apply IHt2].
    destruct (eqb_spec arg x). { subst. symmetry. apply remove_all_shadow. } rewrite remove_all_swap. f_equal. apply IHt2.
  - specialize (IHt1 _ H). specialize (IHt2 _ H). rewrite remove_all_app. rewrite IHt1. f_equal. apply IHt2.
Qed.

Theorem structural_subst_fv : forall x y t t' ft' fy,
  StructuralSubst x y t t' ->
  StructurallyFreeIn t' ft' ->
  StructurallyFreeIn y fy ->
  ~In x fy ->
  ~In x ft'.
Proof.
  intros x y t t' ft' fy [h [Hh Hf]] Hft' Hfy Hiy Hit'.
  generalize dependent y. generalize dependent t'. generalize dependent ft'. generalize dependent fy.
  induction Hh; intros; simpl in *.
  - invert Hf. invert Hft'. destruct Hit'.
  - invert Hf. invert Hft'. destruct Hit'.
  - invert Hf. apply reflect_structural_fv in Hft'. apply reflect_structural_fv in Hfy.
    rewrite Hft' in Hfy. subst. apply Hiy in Hit' as [].
  - invert Hf. invert Hft'. destruct Hit' as [| []]. subst. apply H. reflexivity.
  - invert Hf. invert Hft'. destruct Hit'.
  - invert Hf. invert H6. invert Hft'. invert H4. eapply IHHh; [eassumption | | | eassumption | assumption]; [| eassumption].
    apply in_app_iff in Hit'. destruct (existsb_in _ x va eqb_spec). { assumption. } destruct Hit'. { apply n in H as []. }
    apply wherever_remove_all in H7. subst. apply in_remove_all in H as [].
  - invert Hf. invert Hft'. invert H5. specialize (IHHh1 _ Hiy). specialize (IHHh2 _ Hiy).
    apply in_app_iff in Hit' as [Hi | Hi]. { eapply IHHh1; eassumption. }
    destruct arg. 2: { subst. eapply IHHh2; eassumption. } apply wherever_remove_all in H9. subst.
    apply in_remove_all_neq in Hi; [| intro C; subst; apply H; reflexivity]. eapply IHHh2; eassumption.
  - invert Hf. invert Hft'. invert H5. apply wherever_remove_all in H7. subst.
    apply in_app_iff in Hit' as [Hi | Hi]; [| apply in_remove_all in Hi as []]. eapply IHHh; eassumption.
  - invert Hf. invert Hft'. specialize (IHHh1 _ Hiy). specialize (IHHh2 _ Hiy).
    apply in_app_iff in Hit' as [Hi | Hi]. { eapply IHHh1; eassumption. }
    destruct arg. 2: { subst. eapply IHHh2; eassumption. } apply wherever_remove_all in H8. subst.
    apply in_remove_all_neq in Hi; [| intro C; subst; apply H; reflexivity]. eapply IHHh2; eassumption.
  - invert Hf. invert Hft'. apply in_app_iff in Hit' as [Hi | Hi]; [eapply IHHh1 | eapply IHHh2]; eassumption.
Qed.
