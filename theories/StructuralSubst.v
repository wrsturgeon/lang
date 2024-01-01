From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  FstCmp
  StructuralHole
  Invert
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

Theorem structural_subst_fv : forall x y t,
  ~In x (structural_fv y) ->
  ~In x (structural_fv (structural_subst x y t)).
Proof.
  intros. generalize dependent x. generalize dependent y. induction t; intros; simpl in *; intro C; try solve [destruct C];
  [destruct (eqb_spec id x); subst; simpl in *; [apply H in C as [] |]; destruct C; [| destruct H0]; apply n; assumption | | |];
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
