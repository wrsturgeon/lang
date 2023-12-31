From Coq Require Export
  Lists.List
  Sorting.Permutation.
Export ListNotations.
From Lang Require Import
  Find
  StructuralFreeVariables
  InTactics
  Invert
  StructuralSubst
  Terms.

Variant MaybeStructurallySubst : option string -> term -> term -> term -> Prop :=
  | MaybeSubstNone : forall y t,
      MaybeSubst None y t t
  | MaybeSubstSome : forall t x y t',
      structural_subst x y t = Some t' ->
      MaybeSubst (Some x) y t t'
  .

(* Prevent having two variables with the same name (fst) but different types (snd). *)
Inductive MaybeConsKV {K V} k v : list (K * V) -> list (K * V) -> Prop :=
  | MaybeConsKVCons : forall tl,
      MaybeConsKV k v tl ((k, v) :: tl)
  | MaybeConsKVNil :
      MaybeConsKV k v [] []
  | MaybeConsKVNotEq : forall hdk hdv tl,
      k <> hdk ->
      (* `hdv` can be the same, that's fine: two variables can have the same type *)
      MaybeConsKV k v ((hdk, hdv) :: tl) ((hdk, hdv) :: tl)
  .

Inductive WhereverKV {K V} k v : list (K * V) -> list (K * V) -> Prop :=
  | WhereverKeyHere : forall a b,
      WhereverKV k v a b ->
      WhereverKV k v a ((k, v) :: b)
  | WhereverKeyNil :
      WhereverKV k v [] []
  | WhereverKeyNotEq : forall hdk hdv a b,
      k <> hdk ->
      (* `v` can be the same, that's fine: two variables can have the same type *)
      WhereverKV k v a b ->
      WhereverKV k v ((hdk, hdv) :: a) ((hdk, hdv) :: b)
  .

(* Typed just like in any other programming language (other than Rust). *)
Inductive StructurallyTyped : list (string * term) -> term -> term -> Prop :=
  | STyStar : forall ctx univ,
      StructurallyTyped ctx (TmStar univ) (TmStar (S univ))
  | STyVarS : forall ctx id t,
      FindKV id t ctx ->
      StructurallyTyped ctx (TmVarS id) t
  | STyAtom : forall ctx id,
      StructurallyTyped ctx (TmAtom id) (TmAtom id)
  | STyPack : forall ctx id arg arg_ty curry ty,
      AtomId id curry ->
      StructurallyTyped ctx (TmForA    arg arg_ty curry) ty ->
      StructurallyTyped ctx (TmPack id arg arg_ty curry) ty
  | STyForA : forall ctx arg ty body t kind,
      StructurallyTyped ctx ty kind ->
      StructurallyTyped (match arg with None => ctx | Some a => (a, ty) :: ctx end) body t ->
      StructurallyTyped ctx (TmForA arg ty body) (TmForA arg ty t)
  | STyAppl : forall ctx f x arg ty body substituted,
      StructurallyTyped ctx f (TmForA arg ty body) ->
      StructurallyTyped ctx x ty ->
      MaybeSubst arg x body substituted ->
      StructurallyTyped ctx (TmAppl f x) substituted
  (*
  | STyStar : forall ctx t ty,
      StructurallyTyped ctx t ty ->
      StructurallyTyped ctx t TmStar
  *)
  .
Arguments StructurallyTyped ctx t ty.

(* TODO: CRUCIAL SAFETY THEOREMS: (1) Star n does not have type Star n, and (2) no term has type Void. *)

(* Polymorphic identity function.
 * `\t: *. \x: t. x` is typable (!), and in fact it has type
 * `\t: *. \x: t. t`, almost but not quite the same. Could be simplified to
 * `\t: *. (t -> t)` by making the `x` anonymous. *)
Definition polymorphic_identity_fn := (TmForA (Some "t") (TmStar 0) (TmForA (Some "x") (TmVarS "t") (TmVarS "x")))%string.
Definition polymorphic_identity_ty := (TmForA (Some "t") (TmStar 0) (TmForA (Some "x") (TmVarS "t") (TmVarS "t")))%string.
Arguments polymorphic_identity_fn/.
Arguments polymorphic_identity_ty/.
Theorem dependent_types_woohoo :
  StructurallyTyped [] polymorphic_identity_fn polymorphic_identity_ty.
Proof.
  simpl. eapply STyForA.
  - (* typing `TmStar` *)
    apply STyStar.
  - (* typing the body *)
    eapply STyForA.
    + (* typing `TmVarS "t"` *)
      apply STyVarS. find_kv.
    + (* typing `TmVarS "x" : TmVarS "t"` *)
      apply STyVarS. find_kv.
Qed.

(* Showing that, given f: X -> Y and x: X, we can type (f x) : Y. *)
Example type_fn_app :
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X Y) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fx := TmAppl f x in
  StructurallyTyped ctx fx Y.
Proof. repeat econstructor. intro C. discriminate C. Qed.

(* ...But the above becomes perfectly okay if we add exchange and contraction, i.e., a heap: *)
Example structural_type_allows_reuse :
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X (TmForA None X Y)) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fxx := TmAppl (TmAppl f x) x in
  StructurallyTyped ctx fxx Y.
Proof.
  simpl. eapply STyAppl.
  - eapply STyAppl.
    + apply STyVarS. find_kv.
    + apply STyVarS. find_kv.
    + apply MaybeSubstNone.
  - apply STyVarS. find_kv.
  - apply MaybeSubstNone.
Qed.

Lemma wherever_fst : forall {A B} f s li post,
  @WhereverKV A B s f            li           post ->
  @Wherever   A   s     (map fst li) (map fst post).
Proof. intros. induction H; constructor; assumption. Qed.

Theorem structurally_typed_fv : forall ctx t ty,
  StructurallyTyped ctx t ty ->
  incl (fv_with remove_all t) (map fst ctx).
Proof.
  unfold incl. intros. generalize dependent a. induction H; intros; simpl in *; repeat rewrite slow_down in *;
  try solve [destruct H0]; try (destruct H0; [| destruct H0]; subst; eapply find_kv_in_fst; apply H).
  { apply IHStructurallyTyped. assumption. } 2: {
    apply in_app_iff in H2. destruct H2; [apply IHStructurallyTyped1 | apply IHStructurallyTyped2]; assumption. }
  destruct arg; simpl in *. 2: {
    induction (fv_with remove_all ty); simpl in *. { apply IHStructurallyTyped2. assumption. }
    destruct (existsb (eqb a0) (fv_with remove_all body) || existsb (eqb a0) l)%bool eqn:E; [| destruct H1];
    try (apply IHl; [| assumption]; intros; apply IHStructurallyTyped1; right; assumption).
    apply IHStructurallyTyped1. left. assumption. }
  induction (fv_with remove_all ty); simpl in *.
  - destruct (eqb_spec s a). { subst. apply in_remove_all in H1 as []. }
    apply in_remove_all_neq in H1; [| intro C; subst; contradiction n; reflexivity].
    apply IHStructurallyTyped2 in H1. destruct H1. { subst. contradiction n. reflexivity. } assumption.
  - destruct (existsb_in eqb a0 (remove_all s (fv_with remove_all body)) eqb_spec);
    destruct (existsb_in eqb a0 l eqb_spec); [| | | destruct H1];
    try (apply IHl; [| assumption]; intros; apply IHStructurallyTyped1; right; assumption).
    apply IHStructurallyTyped1. left. assumption.
Qed.

Theorem fv_not_typed : forall ctx t,
  (~incl (fv_with remove_all t) (map fst ctx)) -> ~exists ty, StructurallyTyped ctx t ty.
Proof.
  unfold incl. intros ctx t H [ty C]. generalize dependent H. induction C; intros; simpl in *; try rewrite slow_down in *.
  - apply H. intros. destruct H0.
  - induction H.
    + apply H0. intros. destruct H; [| destruct H]. subst. left. reflexivity.
    + apply IHFindKV. intro C. apply H0. intros. destruct H2; [| destruct H2]. subst. right. apply C. left. reflexivity.
  - apply H. intros. destruct H0.
  - apply IHC. assumption.
  - admit.
  - apply H0. intros. apply in_app_iff in H1. destruct H1.
    + contradiction IHC1. intro C. apply H0. intros. apply C. apply C in H1.

  intros t H [ty C]. remember (@nil (string * term)) as ctx eqn:Ec. generalize dependent Ec. generalize dependent H.
  induction C; intros; subst; simpl in *; try (apply H; reflexivity); try solve [inversion H]; try rewrite slow_down in *.
  { apply IHC; [| reflexivity]. assumption. } 2: {
    destruct (fv_with remove_all f). { apply IHC2; [| reflexivity]. assumption. }
    apply IHC1; [| reflexivity]. intro C. discriminate C. }
  destruct arg; simpl in *. 2: {
    destruct (fv_with remove_all ty); [| apply IHC1; [| reflexivity]; intro C; discriminate C].
    destruct (fv_with remove_all body). { apply H. reflexivity. } apply IHC2; [| reflexivity]. intro C. discriminate C. }
  clear IHC2. destruct (fv_with remove_all ty); simpl in *. 2:{ apply IHC1; [| reflexivity]. intro C. discriminate C. }
  clear IHC1. Abort. (* TODO *)

(* TODO: Substitution (WITH STRUCTURAL RULES, NOT JUST THE USUAL FUNCTION) preserves typing *)
