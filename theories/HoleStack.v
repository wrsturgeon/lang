From Lang Require Import
  Hole
  StructuralHole
  Terms.

Print hole.
Inductive hole_stack : Set :=
  | HoleStackHere
  | HoleStackPack (id : string) (arg : option string) (ty : structural_hole) (curry : list hole_stack)
  | HoleStackForA (arg : option string) (ty : structural_hole) (body : list hole_stack)
  | HoleStackAppl (f : list hole_stack) (x : list hole_stack)
  .

Fixpoint first_hole h :=
  match h with
  | HoleStackHere => SHoleHere
  | HoleStackPack id arg ty curry => SHolePack id arg ty (hd curry)
  end.
