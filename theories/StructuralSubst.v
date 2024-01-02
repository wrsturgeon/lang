From Coq Require Export
  List.
Export ListNotations.
From Coq Require Import
  Ascii.
From Lang Require Import
  FstCmp
  Invert
  NonEmpty
  SplitRemove
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

Inductive StructuralSubst (x : string) : term -> structural_hole -> Prop :=
  | SSubstVoid :
      StructuralSubst x TmVoid (SHoleTerm TmVoid)
  | SSubstStar : forall univ,
      StructuralSubst x (TmStar univ) (SHoleTerm (TmStar univ))
  | SSubstVarSEq :
      StructuralSubst x (TmVarS x) SHoleHere
  | SSubstVarSNEq : forall y,
      x <> y ->
      StructuralSubst x (TmVarS y) (SHoleTerm (TmVarS y))
  | SSubstAtom : forall id,
      StructuralSubst x (TmAtom id) (SHoleTerm (TmAtom id))
  | SSubstPackShadow : forall id ty curry ty',
      StructuralSubst x ty ty' ->
      StructuralSubst x (TmPack id (Some x) ty curry) (SHolePack id (Some x) ty' (SHoleTerm curry))
  | SSubstPack : forall id arg ty curry ty' curry',
      arg <> Some x ->
      StructuralSubst x ty ty' ->
      StructuralSubst x curry curry' ->
      StructuralSubst x (TmPack id arg ty curry) (SHolePack id arg ty' curry')
  | SSubstForAShadow : forall ty body ty',
      StructuralSubst x ty ty' ->
      StructuralSubst x (TmForA (Some x) ty body) (SHoleForA (Some x) ty' (SHoleTerm body))
  | SSubstForA : forall arg ty body ty' body',
      arg <> Some x ->
      StructuralSubst x ty ty' ->
      StructuralSubst x body body' ->
      StructuralSubst x (TmForA arg ty body) (SHoleForA arg ty' body')
  | SSubstAppl : forall f z f' z',
      StructuralSubst x f f' ->
      StructuralSubst x z z' ->
      StructuralSubst x (TmAppl f z) (SHoleAppl f' z')
  .

Theorem reflect_structural_subst : forall x t h,
  structural_subst_hole x t = h <-> StructuralSubst x t h.
Proof.
  split; intros.
  - generalize dependent x. generalize dependent h. induction t; intros; subst; simpl in *; try solve [constructor].
    + destruct (eqb_spec id x). { subst. constructor. } constructor. intro C. subst. apply n. reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. constructor. apply IHt1. reflexivity. }
      constructor; [assumption | apply IHt1 | apply IHt2]; reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. constructor. apply IHt1. reflexivity. }
      constructor; [assumption | apply IHt1 | apply IHt2]; reflexivity.
    + constructor; [apply IHt1 | apply IHt2]; reflexivity.
  - induction H; simpl in *; try rewrite eqb_refl; try rewrite IHStructuralSubst;
    try rewrite IHStructuralSubst1; try rewrite IHStructuralSubst2; try reflexivity.
    + apply eqb_neq in H. rewrite eqb_sym in H. rewrite H. reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. contradiction H. reflexivity. } reflexivity.
    + destruct (eq_opt_spec arg (Some x)). { subst. contradiction H. reflexivity. } reflexivity.
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

Definition structurally_closed t := match structural_fv t with [] => true | _ :: _ => false end.
Arguments structurally_closed/ t.

Definition StructurallyClosed t := StructurallyFreeIn t [].
Arguments StructurallyClosed/ t.

Theorem reflect_structurally_closed : forall t,
  Bool.reflect (StructurallyClosed t) (structurally_closed t).
Proof.
  intros. unfold structurally_closed. unfold StructurallyClosed. remember (structural_fv t) as f eqn:Ef.
  destruct f; constructor. { apply reflect_structural_fv. symmetry. assumption. }
  intro C. apply reflect_structural_fv in C. rewrite <- Ef in C. discriminate C.
Qed.

Lemma ne_intersp_cons : forall {T} li a intersp,
  let f := fun hd => @app T (hd ++ intersp) in
  ne_intersp f (ne_map_hd (cons a) li) = a :: (ne_intersp f li).
Proof. induction li; intros; simpl in *. { reflexivity. } unfold f. simpl. reflexivity. Qed.

Lemma ne_intersp_splitrm : forall {T} (a b : list T) p intersp,
  let f := fun hd => app (hd ++ intersp) in
  ne_intersp f (splitrm_slow p a) ++ ne_intersp f (splitrm_slow p b) = ne_intersp f (splitrm_slow p (a ++ b)).
Proof.
  induction a; intros; simpl in *. { reflexivity. }
  destruct (p a) eqn:E; simpl in *. { unfold f. simpl in *. rewrite <- app_assoc. rewrite IHa. reflexivity. }
  unfold f. repeat rewrite ne_intersp_cons. simpl. f_equal. apply IHa.
Qed.

Lemma splitrm_remove_all : forall li x,
  splitrm_slow (eqb x) (remove_all x li) = NESton (remove_all x li).
Proof.
  induction li; intros; simpl in *. { reflexivity. } destruct (eqb x a) eqn:E. { apply IHli. }
  simpl. rewrite E. rewrite IHli. reflexivity.
Qed.

Lemma splitrm_remove_all_neq : forall li x y,
  x <> y ->
  splitrm_slow (eqb x) (remove_all y li) = ne_map (remove_all y) (splitrm_slow (eqb x) li).
Proof.
  induction li; intros; simpl in *. { reflexivity. } destruct (eqb_spec x a); destruct (eqb_spec y a); subst; simpl in *.
  - contradiction H. reflexivity.
  - rewrite eqb_refl. f_equal. apply IHli. assumption.
  - rewrite IHli; [| assumption]. induction (splitrm_slow (eqb x) li); simpl; rewrite eqb_refl; reflexivity.
  - apply eqb_neq in n. rewrite n. rewrite IHli; [| assumption]. apply eqb_neq in n0.
    induction (splitrm_slow (eqb x) li); simpl; rewrite n0; reflexivity.
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

Theorem structural_subst_fv : forall x y t,
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
