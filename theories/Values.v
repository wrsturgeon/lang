From Adam Require Import
  Terms
  Types.

Inductive Value : term -> Prop :=
  | ValAtom : forall id,
      Value (TmAtom id O)
  | ValPack : forall id arg ty curry ctx x,
      Value x ->
      Value curry ->
      Typed ctx x ty ->
      AtomId id curry ->
      Value (TmAppl (TmPack id arg ty curry) x)
  | ValForA : forall arg ty body,
      Value body -> (* Consider removing this *)
      Value (TmForA arg ty body)
  .

(*
TODO: Define on typing derivations, not terms.
with Value : term -> Prop :=
  | ValAtom : forall id,
      (* NOTE:
       * Must be at level 0: i.e. a term, not a type.
       * In other words, if we want types to reduce,
       * we have to decrement their level before evaluation.
       *)
      Value (TmAtom (AtomId id O))
  | ValApAt : forall id,
      Value (TmAppl (AtomAp arg_t arg_id etc)
  | ValAtom : forall a,
      ValueAtom a ->
      Value (TmAtom a)
  .
*)
