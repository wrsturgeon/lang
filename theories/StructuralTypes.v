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
  | STyForANone : forall ctx ty body t kind,
      StructurallyTyped ctx ty kind ->
      StructurallyTyped ctx body t ->
      StructurallyTyped ctx (TmForA None ty body) (TmForA None ty t)
  | STyForASomeNone : forall ctx arg ty body t kind f,
      StructurallyFreeIn t f ->
      ~In arg f ->
      StructurallyTyped ctx ty kind ->
      StructurallyTyped ((arg, ty) :: ctx) body t ->
      StructurallyTyped ctx (TmForA (Some arg) ty body) (TmForA None ty t)
  | STyForASomeSome : forall ctx arg ty body t kind f,
      StructurallyFreeIn t f ->
      In arg f ->
      StructurallyTyped ctx ty kind ->
      StructurallyTyped ((arg, ty) :: ctx) body t ->
      StructurallyTyped ctx (TmForA (Some arg) ty body) (TmForA (Some arg) ty t)
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
Definition polymorphic_identity_ty := (TmForA (Some "t") (TmStar 0) (TmForA None (TmVarS "t") (TmVarS "t")))%string.
Arguments polymorphic_identity_fn/.
Arguments polymorphic_identity_ty/.
Theorem dependent_types_woohoo :
  StructurallyTyped [] polymorphic_identity_fn polymorphic_identity_ty.
Proof.
  simpl. eapply STyForASomeSome.
  - (* computing free variables *)
    repeat econstructor.
  - (* demonstrating that the type needs to be dependent *)
    simpl. left. reflexivity.
  - (* typing `TmStar` *)
    apply STyStar.
  - (* typing the body *)
    eapply STyForASomeNone.
    + (* computing free variables *)
      repeat econstructor.
    + (* demonstrating that the type does NOT need to be dependent *)
      simpl. intros [C | []]. discriminate C.
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
  induction Ht; intros; simpl in *; invert Hf.
  - destruct Hi.
  - destruct Hi as [Hi | []]. subst. eapply find_kv_in_fst. eassumption.
  - destruct Hi.
  - invert H5. eapply IHHt; [| eassumption]. econstructor; try eassumption. reflexivity.
  - apply in_app_iff in Hi as [Hi | Hi]; [eapply IHHt1 | eapply IHHt2]; eassumption.
  - apply in_app_iff in Hi as [Hi | Hi]. { eapply IHHt1; eassumption. }
    apply wherever_remove_all in H7. subst. destruct (eqb_spec x arg). { subst. apply in_remove_all in Hi as []. }
    apply in_remove_all_neq in Hi; [| assumption]. specialize (IHHt2 _ _ H5 Hi).
    destruct IHHt2. { subst. contradiction n. reflexivity. } assumption.
  - apply in_app_iff in Hi as [Hi | Hi]. { eapply IHHt1; eassumption. }
    apply wherever_remove_all in H7. subst. destruct (eqb_spec x arg). { subst. apply in_remove_all in Hi as []. }
    apply in_remove_all_neq in Hi; [| assumption]. specialize (IHHt2 _ _ H5 Hi).
    destruct IHHt2. { subst. contradiction n. reflexivity. } assumption.
  - apply in_app_iff in Hi as [|]; [eapply IHHt1 | eapply IHHt2]; eassumption.
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
  - apply IHStructurallyTyped.
  - econstructor. { apply IHStructurallyTyped1. } apply IHStructurallyTyped2.
  - econstructor; try eassumption. { apply IHStructurallyTyped1. } apply IHStructurallyTyped2.
  - econstructor; try eassumption. { apply IHStructurallyTyped1. } apply IHStructurallyTyped2.
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
      eapply IHHt2. { reflexivity. } eassumption.
    + econstructor; try eassumption. { eapply IHHt1. { reflexivity. } eassumption. }
      rewrite app_comm_cons. destruct (eqb_spec x arg). { subst. eapply IHHt2. { reflexivity. } constructor. }
      eapply IHHt2. { reflexivity. } constructor; eassumption.
    + econstructor; try eassumption. { eapply IHHt1. { reflexivity. } eassumption. }
      rewrite app_comm_cons. destruct (eqb_spec x arg). { subst. eapply IHHt2. { reflexivity. } constructor. }
      eapply IHHt2. { reflexivity. } constructor; eassumption.
    + econstructor; [eapply IHHt1 | eapply IHHt2 |]; try reflexivity; eassumption.
  - remember (ctxa ++ (x, alt) :: ctxb) as ctx eqn:Ec. generalize dependent alt.
    generalize dependent x. generalize dependent xt. generalize dependent ctxa. generalize dependent ctxb.
    induction Ht; intros; subst; simpl in *; try solve [constructor].
    + constructor. eapply find_kv_app in H; [| apply eqb_spec].
      destruct H as [H | [Hb Ha]]; (eapply find_kv_app; [apply eqb_spec |]). { left. assumption. }
      invert Hb. { apply Ha in Hf as []. } right. split. { assumption. } intros v' C. apply Ha in C as [].
    + constructor. { assumption. } eapply IHHt. { eassumption. } reflexivity.
    + econstructor. { eapply IHHt1. { eassumption. } reflexivity. }
      eapply IHHt2. { eassumption. } reflexivity.
    + econstructor; try eassumption. { eapply IHHt1. { eassumption. } reflexivity. }
      rewrite app_comm_cons. destruct (eqb_spec x arg); subst; (eapply IHHt2; [| reflexivity]); constructor; eassumption.
    + econstructor; try eassumption. { eapply IHHt1. { eassumption. } reflexivity. }
      rewrite app_comm_cons. destruct (eqb_spec x arg); subst; (eapply IHHt2; [| reflexivity]); constructor; eassumption.
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
  - econstructor; [apply IHHt1 | apply IHHt2]; try assumption; reflexivity.
  - econstructor; try eassumption. { apply IHHt1. { assumption. } reflexivity. }
    rewrite app_comm_cons. apply IHHt2. { assumption. } reflexivity.
  - econstructor; try eassumption. { apply IHHt1. { assumption. } reflexivity. }
    rewrite app_comm_cons. apply IHHt2. { assumption. } reflexivity.
  - econstructor; [apply IHHt1 | apply IHHt2 |]; try eassumption; reflexivity.
Qed.

Lemma structurally_typed_irrelevant : forall pre x xt ctx t ty f,
  StructurallyTyped (pre ++ (x, xt) :: ctx) t ty ->
  StructurallyFreeIn t f ->
  ~In x f ->
  StructurallyTyped (pre ++ ctx) t ty.
Proof.
  intros pre x xt ctx t ty f Ht Hf Hi. remember (pre ++ (x, xt) :: ctx) as c eqn:Ec.
  generalize dependent pre. generalize dependent x. generalize dependent xt. generalize dependent ctx.
  generalize dependent f. induction Ht; intros; subst; simpl in *; try solve [constructor].
  - invert Hf. constructor. eapply find_kv_app. { apply eqb_spec. } eapply find_kv_app in H; [| apply eqb_spec].
    destruct H as [H | [Hf Hn]]. { left. assumption. } right. split; [| assumption]. invert Hf; [| assumption].
    contradiction Hi. left. reflexivity.
  - constructor. { assumption. } invert Hf. eapply IHHt; [eassumption | eassumption | reflexivity].
  - invert Hf. rewrite in_app_iff in Hi. econstructor; [eapply IHHt1 | eapply IHHt2]; try reflexivity; try eassumption;
    intro C; apply Hi; [left | right]; assumption.
  - invert Hf. rewrite in_app_iff in Hi. econstructor; try eassumption.
    + eapply IHHt1; [eassumption | | reflexivity]. intro C. apply Hi. left. assumption.
    + destruct (eqb_spec arg x).
      * subst. rewrite app_comm_cons in Ht2. apply <- structural_type_shadow in Ht2. { assumption. } constructor.
      * rewrite app_comm_cons. eapply IHHt2; [eassumption | | reflexivity]. intro C. apply Hi. right. clear IHHt1 IHHt2.
        apply wherever_remove_all in H7. subst. apply in_remove_all_neq. { intro. subst. apply n. reflexivity. } assumption.
  - invert Hf. rewrite in_app_iff in Hi. econstructor; try eassumption.
    + eapply IHHt1; [eassumption | | reflexivity]. intro C. apply Hi. left. assumption.
    + destruct (eqb_spec arg x).
      * subst. rewrite app_comm_cons in Ht2. apply <- structural_type_shadow in Ht2. { assumption. } constructor.
      * rewrite app_comm_cons. eapply IHHt2; [eassumption | | reflexivity]. intro C. apply Hi. right. clear IHHt1 IHHt2.
        apply wherever_remove_all in H7. subst. apply in_remove_all_neq. { intro. subst. apply n. reflexivity. } assumption.
  - invert Hf. rewrite in_app_iff in Hi. econstructor; [eapply IHHt1 | eapply IHHt2 |]; try eassumption; try reflexivity;
    intro C; apply Hi; [left | right]; assumption.
Qed.

Lemma structurally_typed_closed : forall t,
  StructurallyClosed t ->
  forall ctx ty,
  StructurallyTyped ctx t ty ->
  StructurallyTyped [] t ty.
Proof.
  intros. induction ctx. { assumption. } apply IHctx. destruct a.
  eapply (structurally_typed_irrelevant []) in H0. { assumption. } { eassumption. } intros [].
Qed.

Lemma structural_subst_static_type : forall ty,
  StaticType ty ->
  forall x y ty',
  StructuralSubst x y ty ty' ->
  StaticType ty'.
Proof.
  intros ty Ht x y ty' [h [Hh Hf]]. generalize dependent ty. generalize dependent x.
  induction Hf; intros; simpl in *; invert Hh; invert Ht; constructor; try (eapply IHHf2; eassumption);
  (eapply IHHf1; [| eassumption]; assumption).
Qed.

Lemma static_type_kind : forall ty,
  StaticType ty ->
  forall ctx kind,
  StructurallyTyped ctx ty kind ->
  StaticType kind.
Proof.
  intros. generalize dependent H. induction H0; intros; simpl in *; try solve [constructor].
  - invert H0.
  - invert H1.
  - invert H. constructor. { assumption. } apply IHStructurallyTyped2. assumption.
  - invert H1.
  - invert H1.
  - invert H0. invert H. { apply IHStructurallyTyped1 in H3. invert H3. assumption. }
    apply IHStructurallyTyped1 in H3. invert H3.
Qed.

Theorem structural_subst_typed : forall pre x y t t' xt ctx ty,
  StaticType ty ->
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
  - invert Ht; invert Hs.
    + invert Hh. invert Hf. assert (structural_subst x y arg_ty = ty'0). {
        apply reflect_structural_subst. eexists. split; eassumption. } subst.
      assert (A : structural_subst x y arg_ty = arg_ty). { apply reflect_structural_subst.
        eapply structural_subst_not_in. { apply static_type_structurally_closed. assumption. } intros []. }
      rewrite A in *. constructor. { eapply structural_subst_atom_id; [| eassumption]. eexists. split; eassumption. }
      eapply IHHt; [constructor | | eassumption | constructor | eassumption | reflexivity]; try constructor; eassumption.
    + invert Hh; invert Hf; [invert H14; constructor; [assumption |] |
        constructor; [eapply structural_subst_atom_id; [eexists; split |]; eassumption |]];
      (eapply IHHt; [constructor; assumption | | eassumption | constructor; eassumption | eassumption | reflexivity]);
      repeat constructor; assumption.
  - invert Hh. invert Hf. invert Hs. assert (structural_subst x y ty = ty'0). {
      apply reflect_structural_subst. eexists. split; eassumption. }
    subst. assert (A : structural_subst x y ty = ty). { apply reflect_structural_subst.
      eapply structural_subst_not_in. { apply static_type_structurally_closed. assumption. } intros []. }
    repeat rewrite A in *. econstructor.
    + eapply IHHt1; [eapply static_type_kind; [| eassumption] | | | | | reflexivity]; eassumption.
    + eapply IHHt2; [| | | | | reflexivity]; eassumption.
  - invert Hs. invert Hh; invert Hf.
    + invert H10. assert (structural_subst arg y ty = ty'0). { apply reflect_structural_subst. eexists. split; eassumption. }
      subst. assert (A : structural_subst arg y ty = ty). { apply reflect_structural_subst.
        eapply structural_subst_not_in. { apply static_type_structurally_closed. assumption. } intros []. }
      repeat rewrite A in *. econstructor. { apply static_type_structurally_closed. assumption. } { intros []. }
      * eapply IHHt1; [eapply static_type_kind; [| eassumption] | | | | | reflexivity]; eassumption.
      * rewrite app_comm_cons in Ht2. eapply structural_type_shadow in Ht2. { assumption. } constructor.
    + assert (structural_subst x y ty = ty'0). { apply reflect_structural_subst. eexists. split; eassumption. }
      subst. assert (A : structural_subst x y ty = ty). { apply reflect_structural_subst.
        eapply structural_subst_not_in. { apply static_type_structurally_closed. assumption. } intros []. }
      repeat rewrite A in *. econstructor. { apply static_type_structurally_closed. assumption. } { intros []. }
      * eapply IHHt1; [eapply static_type_kind; [| eassumption] | | | | | reflexivity]; eassumption.
      * rewrite app_comm_cons. eapply IHHt2; [| | | | | reflexivity]; try eassumption.
        intros [C | C]. { subst. apply H6. reflexivity. } apply Hi in C as [].
  - invert Hs.
  - invert Hh. invert Hf. clear IHHt1 IHHt2. Abort. (* FUCK *)
