From Lang Require Import
  FreeVariables
  Invert
  StructuralFreeVariables
  Terms.

(* TODO: Not very confident that this definition is right. Scroll down for the more straightforward version.
(* Static, i.e. not (anywhere) dependently typed.
 * Note that this is exactly the same under structural and non-structural interpretation!
 * In either case, we'd use `StructurallyClosed` and `StructurallyStatic` at the type level,
 * and all else is identical boilerplate. *)
Inductive Static : term -> Prop :=
  | StaticVoid :
      Static TmVoid
  | StaticStar : forall univ,
      Static (TmStar univ)
  | StaticVarS : forall x,
      Static (TmVarS x)
  | StaticAtom : forall id,
      Static (TmAtom id)
  | StaticPack : forall id arg ty curry,
      Static (TmForA arg ty curry) ->
      Static (TmPack id arg ty curry)
  | StaticForA : forall arg ty body,
      (* TODO: change this to accept ONLY `TmForA None ...` (note the `None`), then update typing rules s.t. types have `None` iff `curry`/`body` doesn't have `arg` free *)
      StructurallyClosed ty -> (* this is the only line that really matters. NOTE: no matter the context. *)
      Static ty -> (* TODO: Is this necessary? *)
      Static body ->
      Static (TmForA arg ty body)
  | StaticAppl : forall f x,
      Static f ->
      Static x ->
      Static (TmAppl f x)
  .

Fixpoint static t :=
  match t with
  | TmVoid
  | TmStar _
  | TmVarS _
  | TmAtom _ =>
      true
  | TmPack _ _ ty curry
  | TmForA _ ty curry =>
      andb (andb (structurally_closed ty) (static ty)) (static curry)
  | TmAppl f x =>
      andb (static f) (static x)
  end.

Theorem reflect_static : forall t,
  Bool.reflect (Static t) (static t).
Proof.
  induction t; repeat constructor; simpl in *; invert IHt1; invert IHt2;
  repeat rewrite Bool.andb_true_r; repeat rewrite Bool.andb_false_r;
  try (constructor; intro C; invert C; try contradiction; invert H4; contradiction); [| | repeat constructor; assumption];
  destruct (structural_fv t1) eqn:E; assert (A := E); simpl in E; rewrite E; repeat constructor;
  try apply reflect_structural_fv; try assumption; intro C; invert C; [invert H4; rename H7 into H6 |];
  apply reflect_structural_fv in H6; rewrite A in H6; discriminate H6.
Qed.
*)

Inductive StaticType : term -> Prop :=
  | StaticTyVoid :
      StaticType TmVoid
  | StaticTyStar : forall univ,
      StaticType (TmStar univ)
    (* nothing for VarS *)
  | StaticTyAtom : forall id,
      StaticType (TmAtom id)
    (* nothing for Pack *)
  | StaticTyForA : forall ty body,
      StaticType ty -> (* TODO: Can this be inferred from the rest of the definition? *)
      StaticType body ->
      StaticType (TmForA None ty body)
    (* TODO: Is the below rule necessary, or can we just evaluate? *)
  | StaticTyAppl : forall f x,
      StaticType f ->
      StaticType x ->
      StaticType (TmAppl f x)
  .

Lemma static_type_structurally_closed : forall ty,
  StaticType ty ->
  StructurallyClosed ty.
Proof. intros. induction H; simpl in *; econstructor; try rewrite app_nil_r; try reflexivity; assumption. Qed.

Lemma static_type_closed : forall ty,
  StaticType ty ->
  Closed ty.
Proof.
  intros. induction H; simpl in *; econstructor; try rewrite app_nil_r; try constructor; try assumption.
  apply static_type_structurally_closed. assumption.
Qed.
