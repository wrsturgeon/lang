From Coq Require Export
  Lists.List
  Sorting.Permutation.
Export ListNotations.
From Lang Require Import
  Find
  InTactics
  Invert
  Static
  StructuralFreeVariables
  StructuralHole
  StructuralSubst
  Terms.

Variant MaybeStructurallySubst : option string -> term -> term -> term -> Prop :=
  | MaybeSSubstNone : forall y t,
      MaybeStructurallySubst None y t t
  | MaybeSSubstSome : forall x y t t',
      StructuralSubst x y t t' ->
      MaybeStructurallySubst (Some x) y t t'
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
      StructurallyTyped ctx (TmForA arg ty body) (TmForA arg ty t) (* TODO: Maybe `None` if `arg` is not free (used)? *)
  | STyAppl : forall ctx f x arg ty body substituted,
      StructurallyTyped ctx f (TmForA arg ty body) ->
      StructurallyTyped ctx x ty ->
      MaybeStructurallySubst arg x body substituted ->
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
    + apply MaybeSSubstNone.
  - apply STyVarS. find_kv.
  - apply MaybeSSubstNone.
Qed.

Lemma wherever_fst : forall {A B} f s li post,
  @WhereverKV A B s f            li           post ->
  @Wherever   A   s     (map fst li) (map fst post).
Proof. intros. induction H; constructor; assumption. Qed.

Theorem structurally_typed_fv : forall ctx t ty f,
  StructurallyTyped ctx t ty ->
  StructurallyFreeIn t f ->
  incl f (map fst ctx).
Proof.
  unfold incl. intros ctx t ty f Ht Hf x Hi. generalize dependent f. generalize dependent x.
  induction Ht; intros; simpl in *.
  - invert Hf. destruct Hi.
  - invert Hf. destruct Hi as [Hi | []]. subst. eapply find_kv_in_fst. eassumption.
  - invert Hf. destruct Hi.
  - invert Hf. invert H5. invert Ht. eapply IHHt; [| eassumption]. econstructor; try eassumption. reflexivity.
  - invert Hf. apply in_app_iff in Hi as [Hi | Hi]. { eapply IHHt1; eassumption. }
    specialize (IHHt2 x _ H3). destruct arg. 2: { subst. apply IHHt2. assumption. }
    apply wherever_remove_all in H5. subst. destruct (eqb_spec x s). { subst. apply in_remove_all in Hi as []. }
    apply in_remove_all_neq in Hi; [| assumption]. specialize (IHHt2 Hi). destruct IHHt2; [| assumption].
    subst. contradiction n. reflexivity.
  - invert Hf. apply in_app_iff in Hi as [|]; [eapply IHHt1 | eapply IHHt2]; eassumption.
Qed.

Theorem fv_not_typed : forall ctx t f,
  StructurallyFreeIn t f ->
  (~incl f (map fst ctx)) ->
  ~exists ty, StructurallyTyped ctx t ty.
Proof. intros ctx t f Hf Hi [ty C]. eapply structurally_typed_fv in C; [| eassumption]. apply Hi in C as []. Qed.

Lemma structural_subst_atom_id : forall x y t t' id,
  StructuralSubst x y t t' ->
  AtomId id t ->
  AtomId id t'.
Proof.
  intros x y t t' id [h [Hs Hf]] Ha. generalize dependent x. generalize dependent y. generalize dependent t'.
  generalize dependent h. induction Ha; intros; simpl in *. { invert Hs. invert Hf. constructor. }
  invert Hs; invert Hf. { invert H7. constructor. assumption. } constructor. eapply IHHa; eassumption.
Qed.

Lemma structural_type_weakening : forall ctx weaken t ty,
  StructurallyTyped ctx t ty ->
  StructurallyTyped (ctx ++ weaken) t ty.
Proof.
  intros. generalize dependent weaken. induction H; intros; subst; simpl in *; repeat constructor.
  - apply find_kv_weaken. assumption.
  - assumption.
  - invert H0. apply IHStructurallyTyped.
  - econstructor. { apply IHStructurallyTyped1. } destruct arg; apply IHStructurallyTyped2.
  - econstructor; try eassumption. { apply IHStructurallyTyped1. } apply IHStructurallyTyped2.
Qed.

Lemma structural_type_shadow : forall ctxa x alt ctxb xt t ty,
  FindKV x xt ctxa ->
  (StructurallyTyped (ctxa ++ ctxb) t ty <-> StructurallyTyped (ctxa ++ (x, alt) :: ctxb) t ty).
Proof.
  intros ctxa x alt ctxb xt t ty Hf. split; intros Ht.
  - remember (ctxa ++ ctxb) as ctx eqn:Ec. generalize dependent alt.
    generalize dependent x. generalize dependent xt. generalize dependent ctxa. generalize dependent ctxb.
    induction Ht; intros; subst; simpl in *; try solve [constructor].
    + constructor. eapply find_kv_app in H; [| apply eqb_spec].
      destruct H as [H | [Hb Ha]]; (eapply find_kv_app; [apply eqb_spec |]). { left. assumption. }
      right. split; [| assumption]. constructor. { intro C. subst. apply Ha in Hf as []. } assumption.
    + constructor. { assumption. } eapply IHHt. { reflexivity. } eassumption.
    + econstructor. { eapply IHHt1. { reflexivity. } eassumption. }
      destruct arg as [arg |]. 2: { eapply IHHt2. { reflexivity. } eassumption. }
      destruct (eqb_spec x arg); subst; eapply (IHHt2 _ ((arg, ty) :: ctxa)); try reflexivity; constructor; eassumption.
    + econstructor; [eapply IHHt1 | eapply IHHt2 |]; try reflexivity; eassumption.
  - remember (ctxa ++ (x, alt) :: ctxb) as ctx eqn:Ec. generalize dependent alt.
    generalize dependent x. generalize dependent xt. generalize dependent ctxa. generalize dependent ctxb.
    induction Ht; intros; subst; simpl in *; try solve [constructor].
    + constructor. eapply find_kv_app in H; [| apply eqb_spec].
      destruct H as [H | [Hb Ha]]; (eapply find_kv_app; [apply eqb_spec |]). { left. assumption. }
      invert Hb. { apply Ha in Hf as []. } right. split. { assumption. } intros v' C. apply Ha in C as [].
    + constructor. { assumption. } eapply IHHt. { eassumption. } reflexivity.
    + econstructor. { eapply IHHt1. { eassumption. } reflexivity. }
      destruct arg as [arg |]. 2: { eapply IHHt2. { eassumption. } reflexivity. }
      destruct (eqb_spec x arg); subst; eapply (IHHt2 _ ((arg, ty) :: ctxa)); try reflexivity; constructor; eassumption.
    + econstructor; [eapply IHHt1 | eapply IHHt2 |]; try reflexivity; eassumption.
Qed.

Lemma structural_type_exchange : forall pre x xt y yt ctx t ty,
  x <> y ->
  StructurallyTyped (pre ++ (x, xt) :: (y, yt) :: ctx) t ty ->
  StructurallyTyped (pre ++ (y, yt) :: (x, xt) :: ctx) t ty.
Proof.
  intros pre x xt y yt ctx t ty Hn Ht. remember (pre ++ (x, xt) :: (y, yt) :: ctx) as c eqn:Ec.
  generalize dependent pre. generalize dependent x. generalize dependent xt.
  generalize dependent y. generalize dependent yt. generalize dependent ctx.
  induction Ht; intros; subst; simpl in *; try solve [constructor].
  - constructor. apply find_kv_exchange; assumption.
  - constructor. { assumption. } apply IHHt. { assumption. } reflexivity.
  - econstructor. { apply IHHt1. { assumption. } reflexivity. } destruct arg. 2: { apply IHHt2. { assumption. } reflexivity. }
    rewrite app_comm_cons. apply IHHt2. { assumption. } reflexivity.
  - econstructor; [apply IHHt1 | apply IHHt2 |]; try eassumption; reflexivity.
Qed.

Theorem structural_subst_typed : forall pre x y t t' xt ctx ty,
  Static t ->
  (~In x (map fst pre)) ->
  StructuralSubst x y t t' ->
  StructurallyTyped [] y xt ->
  StructurallyTyped (pre ++ (x, xt) :: ctx) t ty ->
  StructurallyTyped (pre ++ ctx) t' ty.
Proof.
  intros pre x y t t' xt ctx ty Hs Hi [h [Hh Hf]] Hy' Ht. remember (pre ++ (x, xt) :: ctx) as c eqn:Ec.
  generalize dependent pre. generalize dependent x. generalize dependent y. generalize dependent t'.
  generalize dependent xt. generalize dependent ctx. generalize dependent Hs. generalize dependent h.
  induction Ht; intros; subst; simpl in *.
  - invert Hh. invert Hf. constructor.
  - invert Hh; invert Hf.
    + destruct pre. { invert H; [| contradiction H2; reflexivity]. apply structural_type_weakening. assumption. }
      eapply find_kv_app in H; [| apply eqb_spec]. destruct H. { apply find_kv_in_fst in H. apply Hi in H as []. }
      destruct H. invert H; [| contradiction H3; reflexivity]. apply (structural_type_weakening []). assumption.
    + constructor. induction pre. { invert H. { contradiction H1. reflexivity. } assumption. }
      destruct a. simpl in *. invert H; constructor. { assumption. }
      apply Decidable.not_or in Hi as [Hx Hi]. apply IHpre; assumption.
  - invert Hh. invert Hf. constructor.
  - invert Ht. invert Hs. invert Hh; invert Hf.
    + invert H11. constructor. { assumption. }
      eapply IHHt; [assumption | | eassumption | | eassumption | reflexivity]; constructor; try eassumption. constructor.
    + constructor. { eapply structural_subst_atom_id; [eexists; split |]; eassumption. }
      eapply IHHt; [assumption | | eassumption | | eassumption | reflexivity]; constructor; eassumption.
  - invert Hs. invert Hh; invert Hf.
    + invert H9. assert (structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists. split; eassumption. }
      subst. assert (structural_subst x y ty = ty). { apply reflect_structural_subst.
        eapply structural_subst_not_in. { eassumption. } intros []. }
      repeat rewrite H in *. econstructor.
      * eapply IHHt1; [| | | | | reflexivity]; eassumption.
      * eapply (structural_type_shadow ((x, ty) :: pre)) in Ht2. { assumption. } constructor.
    + assert (structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists. split; eassumption. } subst.
      assert (structural_subst x y ty = ty). {
        apply reflect_structural_subst. eapply structural_subst_not_in. { eassumption. } intros []. }
      repeat rewrite H in *. econstructor; [eapply IHHt1; [| | | | | reflexivity]; eassumption |].
      destruct arg. 2: { eapply IHHt2; [| | | | | reflexivity]; eassumption. }
      rewrite app_comm_cons. eapply IHHt2; [| | | | | reflexivity]; try eassumption.
      intros [C | C]. { subst. apply H5. reflexivity. } apply Hi in C as [].
  - invert Hs. invert Hh. invert Hf. destruct arg as [arg |]; invert H;
    (econstructor; [eapply IHHt1 | eapply IHHt2 | constructor]); try reflexivity; try eassumption. clear IHHt1 IHHt2.
Abort.

(*
Theorem static_structurally_typed_for_a : forall ctx t arg arg_ty body f,
  Static t ->
  StructurallyClosed t ->
  StructurallyTyped ctx t (TmForA (Some arg) arg_ty body) ->
  StructurallyFreeIn body f ->
  ~In arg f.
Proof.
  intros ctx t arg arg_ty body f Hs Hc Ht Hf Hi. remember (TmForA (Some arg) arg_ty body) as ty eqn:Ety.
  generalize dependent arg. generalize dependent arg_ty. generalize dependent body. generalize dependent f.
  generalize dependent Hs. generalize dependent Hc. induction Ht; intros; subst; try discriminate Ety; simpl in *.
  - invert Hc.
  - invert Hc. invert Hs. eapply IHHt; [assumption | assumption | | reflexivity | eassumption]. assumption.
  - invert Ety. invert Hc. destruct va; destruct vb; invert H6. invert Hs. rename body0 into body_ty. rename arg0 into arg.
    specialize (IHHt1 H2 H6). simpl in *. clear H4.
    induction H5. { eapply IHHt2; try assumption.
    clear Ht2 IHHt1 IHHt2. invert H5. destruct va; destruct vb; invert H8. invert Ht. invert Hs. invert H1.
  - invert Hs. eapply IHHt; try eassumption; [| reflexivity]. intros x C. discriminate C.
  - invert Ety. invert Hs. rename body0 into body_ty. rename arg0 into arg. specialize (IHHt1 Hv).
Qed.
*)

(*
Theorem structural_subst_typed : forall x y t t' xt ctx ty,
  Static t ->
  StructuralSubst x y t t' ->
  FindKV x xt ctx ->
  StructurallyTyped [] y xt ->
  StructurallyTyped ctx t ty ->
  StructurallyTyped ctx t' ty.
Proof.
  intros x y t t' xt ctx ty Hs [h [Hh Hf]] Hc Hy Ht. generalize dependent y. generalize dependent t'.
  generalize dependent xt. generalize dependent ctx. generalize dependent ty. generalize dependent Hs.
  induction Hh; intros; simpl in *; invert Hf; invert Ht; repeat constructor.
  - eapply find_kv_deterministic in Hc; [| eassumption]. subst. apply (structural_type_weakening [] ctx). assumption.
  - assumption.
  - invert H6. assumption.
  - invert H8. invert H6. invert Hs. invert H0. assert (ty'0 = ty); [| subst; econstructor; eassumption].
    assert (structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists; split; eassumption. }
    subst. apply reflect_structural_subst. eapply structural_subst_not_in. { eassumption. } intros [].
  - eapply structural_subst_atom_id; [| eassumption]. eexists. split; eassumption.
  - invert H9. invert Hs. invert H1. assert (structural_subst x y ty = ty'0). {
      apply reflect_structural_subst. eexists. split; eassumption. } subst. assert (structural_subst x y ty = ty). {
      apply reflect_structural_subst. eapply structural_subst_not_in. { eassumption. } intros []. }
    rewrite H0. econstructor. { eassumption. } eapply (IHHh2 _ _ _ _ xt); try eassumption. clear IHHh1 IHHh2.
    destruct arg; [| assumption]. constructor. { intro C. subst. apply H. reflexivity. } assumption.
  - invert Hs. assert (structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists. split; eassumption. }
    subst. assert (structural_subst x y ty = ty). { apply reflect_structural_subst. eapply structural_subst_not_in.
      { eassumption. } intros []. }
    rewrite H in *. econstructor. { eassumption. } invert H5. assumption.
  - shelve.
  - invert Hs. econstructor; [eapply IHHh1 | eapply IHHh2 |]; try eassumption.
    destruct arg; invert H7; constructor. clear IHHh1 IHHh2. destruct (eq_term_spec z x'). { subst. assumption. }
    simpl in *. destruct H0 as [h [Hs Hf]]. eexists. split. { eassumption. } Search h. Search body.
    invert H2.
    + invert Hh1. { invert H1. invert H3. invert H.

    simpl in *.
    Search s.
    destruct H0 as [h [Hh Hf]].
    eexists. split. { eassumption. } apply structural_subst_not_in. assert (~In  Search StructuralSubst.
    (* idea is that structurally substituting something twice is identity *) Search ty. Search StructuralSubstHole.

  intros x y t t' xt ctx ty Hs [h [Hh Hf]] Hc Hy Ht. generalize dependent x. generalize dependent y.
  generalize dependent t'. generalize dependent xt. generalize dependent h. generalize dependent Hs.
  induction Ht; intros; simpl in *; invert Hh; invert Hf; repeat constructor.
  - eapply find_kv_deterministic in H; [| eassumption]. subst. assumption.
  - assumption.
  - invert H8. assumption.
  - invert H8. invert Ht. invert Hs. invert H1. simpl in *.
    assert (A : StructuralSubst x y arg_ty arg_ty). { eapply structural_subst_not_in. { eassumption. } intros []. }
    apply reflect_structural_subst in A. assert (A2 : structural_subst x y arg_ty = ty'0). {
      apply reflect_structural_subst. eexists. split; eassumption. }
    rewrite A2 in A. clear A2. subst. econstructor; eassumption.
  - eapply structural_subst_atom_id; [| eassumption]. eexists; split; eassumption.
  - invert Hs. eapply IHHt; clear IHHt; try eassumption; constructor; eassumption.
  - invert H6. invert Hs. assert (A : ty'0 = ty); [| subst; econstructor; eassumption].
    assert (A : structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists; split; eassumption. }
    subst. apply reflect_structural_subst. eapply structural_subst_not_in. { eassumption. } intros [].
  - invert Hs. assert (ty'0 = ty). { clear IHHt1 IHHt2.
      assert (structural_subst x y ty = ty'0); subst; apply reflect_structural_subst.
      { eexists; split; eassumption. } eapply structural_subst_not_in. { eassumption. } intros []. }
    subst. econstructor. { eassumption. } eapply IHHt2; clear IHHt1 IHHt2; try eassumption. 2: {
      destruct arg. { constructor. { intro C. subst. apply H2. reflexivity. } eassumption. } assumption. }
    destruct arg. 2: { assumption. } generalize depende
    assert (body'0 = body); [| subst; assumption].
    assert (structural_subst x y body = body'0); subst; apply reflect_structural_subst. { eexists; split; eassumption. }
    eapply structural_subst_not_in. { eassumption. }
Qed.
*)
