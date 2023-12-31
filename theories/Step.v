From Lang Require Import
  Invert
  PartitionKV
  Subst
  Terms
  Values.

Inductive Step : list (string * term) -> term -> list (string * term) -> term -> Prop :=
  | StepVarS : forall id val,
      Step [(id, val)] (TmVarS id) [] val
  | StepPack : forall ctx arg ty curry ctx' arg' ty' curry' id,
      Step ctx (TmForA arg ty curry) ctx' (TmForA arg' ty' curry') ->
      Step ctx (TmPack id arg ty curry) ctx' (TmPack id arg' ty' curry')
  | StepForATy : forall ctx ty ctx' ty' arg curry,
      Step ctx ty ctx' ty' ->
      Step ctx (TmForA arg ty curry) ctx' (TmForA arg ty' curry)
  | StepForACurry : forall ctx curry ctx' curry' arg ty,
      Step ctx curry ctx' curry' ->
      Step ctx (TmForA arg ty curry) ctx' (TmForA arg ty curry')
  | StepForAAppl : forall v pf ctxt ctxc ctx arg ty curry out,
      Value v ->
      PartitionKV pf ctxt ctxc ->
      ctx = pf ++ ctxc ->
      match arg with
      | None => curry = out
      | Some x => subst x v curry = Some out
      end ->
      Step ctx (TmAppl (TmForA arg ty curry) v) ctxc out
  | StepApplF : forall ctxf f ctxf' f' ctxx ctx ctx' x,
      Step ctxf f ctxf' f' ->
      ctxf ++ ctxx = ctx ->
      ctxf' ++ ctxx = ctx' ->
      Step ctx (TmAppl f x) ctx' (TmAppl f' x)
  | StepApplX : forall ctxx x ctxx' x' ctxf ctx ctx' f,
      Step ctxx x ctxx' x' ->
      ctxf ++ ctxx = ctx ->
      ctxf ++ ctxx' = ctx' ->
      Step ctx (TmAppl f x) ctx' (TmAppl f x')
  .

(* Reflexive transitive closure on `Step` *)
Inductive MultiStep : list (string * term) -> term -> list (string * term) -> term -> Prop :=
  | MultiStepRefl : forall ctx t,
      MultiStep ctx t ctx t
  | MultiStepTrans : forall ctx t ctx' t' ctx'' t'',
      Step ctx t ctx' t' ->
      MultiStep ctx' t' ctx'' t'' ->
      MultiStep ctx t ctx'' t''
  .

Theorem values_cant_step : forall v,
  Value v ->
  forall ctx ctx' v',
  ~Step ctx v ctx' v'.
Proof.
  intros v Hv. induction Hv; intros; simpl in *; intro C; try solve [invert C].
  - invert C. eapply IHHv. apply H7.
  - invert C; [eapply IHHv1 | eapply IHHv2]; apply H5.
  - invert C; [eapply IHHv1 | eapply IHHv2]; apply H1.
Qed.
