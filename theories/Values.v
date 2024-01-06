From Coq Require Export
  List.
Export ListNotations.
From Coq Require
  Program.Wf.
From Lang Require Import
  FreeVariables
  Invert
  StructuralFreeVariables
  Terms.

Inductive Value : term -> Prop :=
  | ValStar : forall univ,
      Value (TmStar univ)
  | ValAtom : forall id,
      Value (TmAtom id)
  | ValPack : forall id arg ty curry,
      AtomId id curry ->
      Value (TmForA    arg ty curry) ->
      Value (TmPack id arg ty curry)
  | ValForA : forall arg ty body,
      let fora := TmForA arg ty body in
      Value ty ->
      Value body -> (* Consider removing this *)
      Value fora
  | ValApplPack : forall id arg ty curry x,
      let pack := TmPack id arg ty curry in
      let appl := TmAppl pack x in
      Value pack ->
      Value x ->
      Value appl
  .

Fixpoint is_value t :=
  match t with
  | TmVoid
  | TmVarS _ =>
      false
  | TmStar _
  | TmAtom _ =>
      true
  | TmPack id arg ty curry =>
      match atom_id curry with
      | None => false
      | Some aid => andb (eqb id aid) (andb (is_value ty) (is_value curry))
      end
  | TmForA arg ty body =>
      andb (is_value ty) (is_value body)
  | TmAppl (TmPack id arg ty curry) x =>
      match atom_id curry with
      | None => false
      | Some aid => andb (is_value x) (andb (eqb id aid) (andb (is_value ty) (is_value curry)))
      end
  | TmAppl _ _ =>
      false
  end.

Theorem reflect_value : forall t,
  Bool.reflect (Value t) (is_value t).
Proof.
  induction t; simpl in *; repeat constructor; try solve [intro C; inversion C].
  - destruct (atom_id t2) eqn:A. 2: {
      constructor. intro C. invert C. eapply reflect_not_atom_id in A. apply A in H1 as []. }
    destruct (eqb_spec id s). 2: {
      constructor. intro C. invert C. apply reflect_atom_id in H1. rewrite A in H1. invert H1. apply n. reflexivity. }
    subst. simpl. destruct IHt1. 2: { constructor. intro C. invert C. invert H4. apply n in H2 as []. }
    destruct IHt2. 2: { constructor. intro C. invert C. invert H4. apply n in H5 as []. }
    constructor. constructor. { apply reflect_atom_id. assumption. } constructor; assumption.
  - destruct IHt1. 2: { constructor. intro C. invert C. apply n in H1 as []. }
    destruct IHt2. 2: { constructor. intro C. invert C. apply n in H3 as []. }
    constructor. constructor; assumption.
  - destruct t1; try (constructor; intro C; inversion C). rename t1_1 into ty. rename t1_2 into curry. simpl in *.
    destruct (atom_id curry) eqn:A. 2: { invert IHt1. constructor. intro C. invert C. apply H in H2 as []. }
    destruct (eqb id s). 2: {
      invert IHt1. simpl. rewrite Bool.andb_false_r. constructor. intro C. invert C. apply H in H2 as []. }
    destruct IHt2. 2: { constructor. intro C. invert C. apply n in H5 as []. }
    invert IHt1; constructor. { constructor; assumption. } intro C. invert C. apply H0 in H3 as [].
Qed.

Theorem values_structurally_closed : forall v,
  Value v ->
  StructurallyClosed v.
Proof.
  intros v Hv. induction Hv; simpl in *; try solve [repeat constructor].
  - constructor. assumption.
  - unfold fora. clear fora. econstructor; [eassumption | eassumption | destruct arg; constructor | reflexivity].
  - unfold appl. clear appl. econstructor; [eassumption | eassumption | reflexivity].
Qed.

Theorem values_closed : forall v,
  Value v ->
  Closed v.
Proof.
  intros v Hv. induction Hv; simpl in *; try solve [repeat constructor].
  - constructor. assumption.
  - unfold fora. clear fora. econstructor; [apply values_structurally_closed; assumption |
      eassumption | constructor | reflexivity | destruct arg; constructor].
  - unfold appl. clear appl. unfold pack in *. clear pack. econstructor; [eassumption | eassumption | reflexivity].
Qed.
