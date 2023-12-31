From Lang Require Import
  Terms.

Inductive hole : Set :=
  | HoleHere
  | HolePackTy (id : string) (arg : option string) (curry : term)
  | HolePackCurry (id : string) (arg : option string) (ty : term)
  | HoleForATy (arg : option string) (body : term)
  | HoleForABody (arg : option string) (ty : term)
  | HoleApplF (x : term)
  | HoleApplX (f : term)
  .

Definition fill : hole -> term -> term := fun h t =>
  match h with
  | HoleHere => t
  | HolePackTy id arg curry => TmPack id arg t curry
  | HolePackCurry id arg ty => TmPack id arg ty t
  | HoleForATy arg body => TmForA arg t body
  | HoleForABody arg ty => TmForA arg ty t
  | HoleApplF x => TmAppl t x
  | HoleApplX f => TmAppl f t
  end.

Inductive Fill : hole -> term -> term -> Prop :=
  | FillHere : forall t,
      Fill HoleHere t t
  | FillPackTy : forall id arg ty curry,
      Fill (HolePackTy id arg curry) ty (TmPack id arg ty curry)
  | FillPackCurry : forall id arg ty curry,
      Fill (HolePackCurry id arg ty) curry (TmPack id arg ty curry)
  | FillForATy : forall arg ty body,
      Fill (HoleForATy arg body) ty (TmForA arg ty body)
  | FillForABody : forall arg ty body,
      Fill (HoleForABody arg ty) body (TmForA arg ty body)
  | FillApplF : forall f x,
      Fill (HoleApplF x) f (TmAppl f x)
  | FillApplX : forall f x,
      Fill (HoleApplX f) x (TmAppl f x)
  .

Theorem reflect_fill : forall h t t',
  fill h t = t' <-> Fill h t t'.
Proof.
  split; intros.
  - destruct h; subst; constructor.
  - destruct H; reflexivity.
Qed.
