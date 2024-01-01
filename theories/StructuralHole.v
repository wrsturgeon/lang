From Lang Require Import
  Hole
  Invert
  Terms.

Inductive structural_hole : Set :=
  | SHoleHere
  | SHoleTerm (tm : term)
  | SHolePack (id : string) (arg : option string) (ty : structural_hole) (curry : structural_hole)
  | SHoleForA (arg : option string) (ty : structural_hole) (body : structural_hole)
  | SHoleAppl (f : structural_hole) (x : structural_hole)
  .

Fixpoint sfill h t : term :=
  match h with
  | SHoleHere => t
  | SHoleTerm tm => tm
  | SHolePack id arg ty curry => TmPack id arg (sfill ty t) (sfill curry t)
  | SHoleForA arg ty body => TmForA arg (sfill ty t) (sfill body t)
  | SHoleAppl f x => TmAppl (sfill f t) (sfill x t)
  end.

Inductive StructuralFill : structural_hole -> term -> term -> Prop :=
  | SFillHere : forall t,
      StructuralFill SHoleHere t t
  | SFillNone : forall t tm,
      StructuralFill (SHoleTerm tm) t tm
  | SFillPack : forall t id arg ty curry ty' curry',
      StructuralFill ty t ty' ->
      StructuralFill curry t curry' ->
      StructuralFill (SHolePack id arg ty curry) t (TmPack id arg ty' curry')
  | SFillForA : forall t arg ty body ty' body',
      StructuralFill ty t ty' ->
      StructuralFill body t body' ->
      StructuralFill (SHoleForA arg ty body) t (TmForA arg ty' body')
  | SFillAppl : forall t f x f' x',
      StructuralFill f t f' ->
      StructuralFill x t x' ->
      StructuralFill (SHoleAppl f x) t (TmAppl f' x')
  .

Theorem reflect_sfill : forall h t t',
  sfill h t = t' <-> StructuralFill h t t'.
Proof.
  split; intros.
  - generalize dependent t. generalize dependent t'.
    induction h; intros; subst; simpl in *; constructor; try apply IHh1; try apply IHh2; reflexivity.
  - induction H; simpl in *; try rewrite IHStructuralFill1; try rewrite IHStructuralFill2; reflexivity.
Qed.

Fixpoint eq_shole a b :=
  match a, b with
  | SHoleHere, SHoleHere =>
      true
  | SHoleTerm ta, SHoleTerm tb =>
      eq_term ta tb
  | SHolePack ida arga tya currya, SHolePack idb argb tyb curryb =>
      andb (eqb ida idb) (andb (eq_opt arga argb) (andb (eq_shole tya tyb) (eq_shole currya curryb)))
  | SHoleForA arga tya currya, SHoleForA argb tyb curryb =>
      andb (eq_opt arga argb) (andb (eq_shole tya tyb) (eq_shole currya curryb))
  | SHoleAppl fa xa, SHoleAppl fb xb =>
      andb (eq_shole fa fb) (eq_shole xa xb)
  | _, _ => false
  end.

Theorem eq_shole_spec : forall a b,
  Bool.reflect (a = b) (eq_shole a b).
Proof.
  induction a; intros []; simpl in *; try solve [constructor; try reflexivity; try (intro C; discriminate C)];
  try (destruct (eq_term_spec tm tm0); [| rf n]);
  try (destruct (eqb_spec id id0); [| rf n]);
  try (destruct (eq_opt_spec arg arg0); [| rf n]);
  try (destruct (IHa1 ty); [| rf n]);
  try (destruct (IHa2 curry); [| rf n]);
  try (destruct (IHa2 body); [| rf n]);
  try (destruct (IHa1 f); [| rf n]);
  try (destruct (IHa2 x); [| rf n]);
  constructor; subst; reflexivity.
Qed.

Fixpoint structuralize h :=
  match h with
  | HoleHere => SHoleHere
  | HolePackTy id arg ty curry => SHolePack id arg (structuralize ty) (SHoleTerm curry)
  | HolePackCurry id arg ty curry => SHolePack id arg (SHoleTerm ty) (structuralize curry)
  | HoleForATy arg ty body => SHoleForA arg (structuralize ty) (SHoleTerm body)
  | HoleForABody arg ty body => SHoleForA arg (SHoleTerm ty) (structuralize body)
  | HoleApplF f x => SHoleAppl (structuralize f) (SHoleTerm x)
  | HoleApplX f x => SHoleAppl (SHoleTerm f) (structuralize x)
  end.

Theorem structuralize_invariant : forall h t,
  fill h t = sfill (structuralize h) t.
Proof. induction h; intros; simpl in *; try rewrite IHh; reflexivity. Qed.
