From Lang Require Import
  Invert
  Terms.

Inductive hole : Set :=
  | HoleHere
  | HolePackTy (id : string) (arg : option string) (ty : hole) (curry : term)
  | HolePackCurry (id : string) (arg : option string) (ty : term) (curry : hole)
  | HoleForATy (arg : option string) (ty : hole) (body : term)
  | HoleForABody (arg : option string) (ty : term) (body : hole)
  | HoleApplF (f : hole) (x : term)
  | HoleApplX (f : term) (x : hole)
  .

Fixpoint fill h t : term :=
  match h with
  | HoleHere => t
  | HolePackTy id arg ty curry => TmPack id arg (fill ty t) curry
  | HolePackCurry id arg ty curry => TmPack id arg ty (fill curry t)
  | HoleForATy arg ty body => TmForA arg (fill ty t) body
  | HoleForABody arg ty body => TmForA arg ty (fill body t)
  | HoleApplF f x => TmAppl (fill f t) x
  | HoleApplX f x => TmAppl f (fill x t)
  end.

Inductive Fill : hole -> term -> term -> Prop :=
  | FillHere : forall t,
      Fill HoleHere t t
  | FillPackTy : forall t id arg ty curry ty',
      Fill ty t ty' ->
      Fill (HolePackTy id arg ty curry) t (TmPack id arg ty' curry)
  | FillPackCurry : forall t id arg ty curry curry',
      Fill curry t curry' ->
      Fill (HolePackCurry id arg ty curry) t (TmPack id arg ty curry')
  | FillForATy : forall t arg ty body ty',
      Fill ty t ty' ->
      Fill (HoleForATy arg ty body) t (TmForA arg ty' body)
  | FillForABody : forall t arg ty body body',
      Fill body t body' ->
      Fill (HoleForABody arg ty body) t (TmForA arg ty body')
  | FillApplF : forall t f x f',
      Fill f t f' ->
      Fill (HoleApplF f x) t (TmAppl f' x)
  | FillApplX : forall t f x x',
      Fill x t x' ->
      Fill (HoleApplX f x) t (TmAppl f x')
  .

Theorem reflect_fill : forall h t t',
  fill h t = t' <-> Fill h t t'.
Proof.
  split; intros.
  - generalize dependent t. generalize dependent t'.
    induction h; intros; subst; simpl in *; constructor; apply IHh; reflexivity.
  - induction H; simpl in *; try rewrite IHFill; reflexivity.
Qed.

Fixpoint eq_hole a b :=
  match a, b with
  | HoleHere, HoleHere =>
      true
  | HolePackTy ida arga tya currya, HolePackTy idb argb tyb curryb =>
      andb (eqb ida idb) (andb (eq_opt arga argb) (andb (eq_hole tya tyb) (eq_term currya curryb)))
  | HolePackCurry ida arga tya currya, HolePackCurry idb argb tyb curryb =>
      andb (eqb ida idb) (andb (eq_opt arga argb) (andb (eq_term tya tyb) (eq_hole currya curryb)))
  | HoleForATy arga tya currya, HoleForATy argb tyb curryb =>
      andb (eq_opt arga argb) (andb (eq_hole tya tyb) (eq_term currya curryb))
  | HoleForABody arga tya currya, HoleForABody argb tyb curryb =>
      andb (eq_opt arga argb) (andb (eq_term tya tyb) (eq_hole currya curryb))
  | HoleApplF fa xa, HoleApplF fb xb =>
      andb (eq_hole fa fb) (eq_term xa xb)
  | HoleApplX fa xa, HoleApplX fb xb =>
      andb (eq_term fa fb) (eq_hole xa xb)
  | _, _ => false
  end.

Ltac rf n := constructor; intros C; invert C; apply n; reflexivity.
Theorem eq_hole_spec : forall a b,
  Bool.reflect (a = b) (eq_hole a b).
Proof.
  induction a; intros []; simpl in *; try solve [constructor; try reflexivity; try (intro C; discriminate C)];
  try (destruct (eqb_spec id id0); [| rf n]);
  try (destruct (eq_opt_spec arg arg0); [| rf n]);
  try (destruct (IHa ty); [| rf n]);
  try (destruct (eq_term_spec curry curry0); [| rf n]);
  try (destruct (eq_term_spec ty ty0); [| rf n]);
  try (destruct (IHa curry); [| rf n]);
  try (destruct (eq_term_spec body body0); [| rf n]);
  try (destruct (IHa body); [| rf n]);
  try (destruct (IHa f); [| rf n]);
  try (destruct (eq_term_spec x x0); [| rf n]);
  try (destruct (eq_term_spec f f0); [| rf n]);
  try (destruct (IHa x); [| rf n]);
  constructor; subst; reflexivity.
Qed.
