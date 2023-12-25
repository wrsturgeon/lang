From Lang Require Import
  Invert
  Terms
  Types.

(*
Theorem no_type_in_type : forall ctx,
  ~Typed ctx TmStar TmStar.
Proof.
  intros ctx C. remember TmStar as t eqn:Et. remember TmStar as ty eqn:Ety. rewrite Et in C at 2.
  induction C; intros; simpl in *; subst; try discriminate.
  (* inversion C. subst. apply IHC; reflexivity. *)
Qed.

Theorem BAD_exists_term_typed_void : exists t,
  Typed [] t TmVoid.
Proof.
  eexists. Check TyApplNone. eapply (TyApplNone [] [] [] _ _ (TmAtom "")); try reflexivity.
  - econstructor. { constructor. }
  - eapply (TyApplNone [] [] []); try reflexivity.
Qed.

Theorem no_term_typed_void : forall t,
  ~Typed [] t TmVoid.
Proof.
  intros t C. remember TmVoid as ty eqn:Et. remember [] as ctx eqn:Ec.
  generalize dependent Ec. generalize dependent Et. induction C; intros; simpl in *; subst; try discriminate;
  (* At this point, only function application is left *)
  destruct ctxf; destruct ctxx; invert Ec.
  - clear IHC1. induction ty; try apply (IHC2 eq_refl eq_refl); clear IHC2.
    + 
  - clear IHC1. invert C1; try (destruct ctxt; destruct ctxc; invert H6).
    + clear IHC1.

  - clear IHC1. generalize dependent x. generalize dependent IHC2.
    remember [] as ctx eqn:Ec. generalize dependent Ec.
    remember (TmForA None ty TmVoid) as fora eqn:Ef. generalize dependent ty.
    induction C1; intros; simpl in *; try discriminate.
    + invert Ef. clear IHC1_2. destruct ctxt; destruct ctxc; invert Ec; simpl in *.
      apply IHC2; try reflexivity.
      eapply IHC1_1; try reflexivity.
    + destruct ctxt; destruct ctxc; invert H6.
Qed.
*)
