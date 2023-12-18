From Lang Require Import
  Terms.

Variant TypecheckResult :=
  | TCRVariable : string -> TypecheckResult
  | TCRClosed : term -> TypecheckResult
  .

Print term.
Fixpoint typecheck t :=
  match t with
  | TmVoid => TmStar
  | TmStar => 
  end.
