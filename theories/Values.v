From Lang Require Import
  Terms
  Types.

Inductive Value : term -> Prop :=
  | ValAtom : forall id,
      Value (TmAtom id)
  | ValPack : forall id arg arg_ty curry x ty,
      let pack := TmPack id arg arg_ty curry in
      let appl := TmAppl pack x in
      Value x ->
      Value curry ->
      AtomId id curry ->
      Typed [] appl ty ->
      Value appl
  | ValForA : forall arg arg_ty body ty,
      let fora := TmForA arg arg_ty body in
      Value body -> (* Consider removing this *)
      Typed [] fora ty ->
      Value fora
  .

Theorem values_always_typed : forall v,
  Value v ->
  exists ty, Typed [] v ty.
Proof.
  intros. induction H.
  - exists (TmAtom id). constructor.
  - exists ty. assumption.
  - exists ty. assumption.
Qed.
