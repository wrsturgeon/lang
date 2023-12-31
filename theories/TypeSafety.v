From Lang Require Import
  Find
  Invert
  PartitionKV
  Step
  Terms
  Types
  Values.

Lemma typed_empty_wherever : forall t ty,
  Typed [] t ty ->
  TypedWith WhereverKV [] [] t ty.
Proof.
  intros. simpl in *. remember MaybeConsKV as m eqn:Em. generalize dependent Em.
  remember [] as e eqn:Ee. generalize dependent Ee.
  remember [] as c eqn:Ec. generalize dependent Ec.
  induction H; intros; subst; simpl in *; try solve [constructor]; try contradiction H.
  1:{ constructor. { assumption. } apply IHTypedWith; reflexivity. }
  2:{ destruct ctxf; destruct ctxx; invert Ec.
      econstructor; [apply IHTypedWith1 | apply IHTypedWith2 | | assumption]; reflexivity. }
  destruct pf; destruct ctxc; invert Ec. invert H2; [| invert H3 | invert H4].
  econstructor; [apply H | | destruct arg; [constructor | reflexivity] | apply PartitionKVDone | reflexivity].
  destruct arg. 2: { subst. apply IHTypedWith2; reflexivity. } invert H1. 2: { apply IHTypedWith2; reflexivity. }
Abort.

Theorem values_always_typed : forall v,
  Value v ->
  exists ty, Typed [] v ty.
Proof.
  intros. induction H.
  1:{ exists (TmStar (S univ)). constructor. }
  1:{ exists (TmAtom id). constructor. }
  1:{ destruct IHValue as [t IH]. exists t. econstructor; assumption. }
  2:{ destruct IHValue1 as [t1 H1]. destruct IHValue2 as [t2 H2]. invert H1; [| destruct H3]. invert H10; [| destruct H1].
      destruct pf; destruct ctxc; invert H13. invert H12; [| invert H1 | invert H3]. eexists. econstructor.
      1:{ constructor. { assumption. } econstructor. { apply H5. } { apply H6. } { apply H8. } { constructor. } reflexivity. }
      2:{ reflexivity. }
      econstructor. { constructor. { assumption. } invert H10. apply H10.
  - destruct IHValue1 as [t1 IH1]. destruct IHValue2 as [t2 IH2]. eexists.
    econstructor; [| apply IH2 | destruct arg; [apply MaybeConsKVNil | reflexivity] | apply PartitionKVDone | reflexivity].
  - exists ty. assumption.
Qed.

Theorem progress : forall ctx t ty,
  Typed ctx t ty ->
  (Value t \/ exists ctx' t', Step ctx t ctx' t').
Proof.
  intros ctx t ty Ht. induction Ht; intros; simpl in *.
  - left. constructor.
  - right. exists []. exists t. constructor.
  - left. constructor.
  - right. left. constructor.
Qed.

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
