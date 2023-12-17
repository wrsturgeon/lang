(*
From Adam Require Import
  Invert
  Snoc
  Terms
  TypecheckDef.

(* Infer the minimal variables that need to be in context, in order, for a term to typecheck. *)
Fixpoint gen_context_acc (provided acc : list string) t :=
  match t with
  | TmVarS s =>
      match provided with
      | v :: tl => if eqb s v then (tl, acc) else (provided, snoc s acc)
      | [] => (provided, snoc s acc)
      end
  | TmPack _ arg ty curry
  | TmForA arg ty curry =>
      let (p, a) := gen_context_acc provided acc ty in
      let ext := match arg with Some x => x :: p | None => p end in
      gen_context_acc ext a curry
  | TmAppl f x =>
      let (p, a) := gen_context_acc provided acc f in
      gen_context_acc p a x
  | _ =>
      (provided, acc)
  end.
Definition gen_context : term -> list string := fun t => let (_, c) := gen_context_acc [] [] t in c.
(* Arguments gen_context t/. *)

Fixpoint lzip {A B} (a : list A) (b : list B) :=
  match a, b with
  | [], [] => Some []
  | hdl :: tll, hdr :: tlr => option_map (cons (hdl, hdr)) (lzip tll tlr)
  | _, _ => None
  end.

Theorem gen_context_correct : forall t ty,
  (exists ctx ctx', typecheck ctx t = Some (ty, ctx')) ->
  exists types, forall fused,
  lzip (gen_context t) types = Some fused ->
  typecheck fused t = Some (ty, []).
Proof.
  intros t ty [ctx [ctx' H]]. generalize dependent ty. generalize dependent ctx'. generalize dependent ctx.
  induction t; intros; try solve [invert H].
  - destruct ctx; intros; try discriminate H. destruct p. simpl in H.
    destruct (eqb id s) eqn:E; try discriminate H. apply eqb_eq in E. subst. invert H.
    exists [ty]. intros. invert H. simpl. rewrite eqb_refl. reflexivity.
  - simpl in H. invert H. exists []. intros. invert H. reflexivity.
  - simpl in H. simpl. destruct (atom_id t2) eqn:Ea; try discriminate H.
    destruct (eqb id s) eqn:E; try discriminate H. destruct arg; simpl.
    + unfold bind_all_to_void in H. destruct (typecheck ((s0, t1) :: bind_all_to_void ctx) t2) eqn:Et. destruct p. invert H. simpl.
  - unfold gen_context. simpl in *. invert H.
    + apply IHt2 in H6. destruct H6 as [ty H]. eexists. econstructor; try assumption.
  - unfold gen_context. invert H; apply IHt2 in H6; destruct H6 as [ty H]; simpl in *; econstructor.
Qed.
*)
