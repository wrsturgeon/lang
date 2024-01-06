From Coq Require Export
  Lists.List
  Sorting.Permutation.
Export ListNotations.
From Lang Require Import
  Find
  FreeVariables
  Invert
  Partition
  PartitionKV
  StructuralTypes
  Subst
  Terms.

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

(*
Variant MaybeSubst : option string -> term -> term -> term -> Prop :=
  | MaybeSubstNone : forall y t,
      MaybeSubst None y t t
  | MaybeSubstSome : forall x y t t',
      Subst x y t t' ->
      MaybeSubst (Some x) y t t'
  .

(* Typed extremely strictly, as if on a stack: no exchange, no weakening, no contraction. *)
Inductive Typed : list (string * term) -> term -> term -> Prop :=
  | TyStar : forall univ,
      Typed [] (TmStar univ) (TmStar (S univ))
  | TyVarS : forall id t,
      Typed [(id, t)] (TmVarS id) t
  | TyAtom : forall id,
      Typed [] (TmAtom id) (TmAtom id)
  | TyPack : forall ctx id arg arg_ty curry ty,
      AtomId id curry ->
      Typed ctx (TmForA    arg arg_ty curry) ty ->
      Typed ctx (TmPack id arg arg_ty curry) ty
  | TyForA : forall pf ctx ctxt ctxc ctxa arg ty body t kind,
      StructurallyTyped ctxt ty kind ->
      Typed ctxa body t ->
      ctxa = match arg with None => ctxc | Some a => (a, ty) :: ctxc end ->
      PartitionKV pf ctxt ctxc ->
      ctx = pf ++ ctxc ->
      Typed ctx (TmForA arg ty body) (TmForA arg ty t)
  | TyAppl : forall ctx ctxf ctxx f x arg ty body substituted,
      Typed ctxf f (TmForA arg ty body) ->
      Typed ctxx x ty ->
      ctxf ++ ctxx = ctx ->
      MaybeSubst arg x body substituted ->
      Typed ctx (TmAppl f x) substituted
  (*
  | TyStar : forall ctx t ty,
      Typed ctx t ty ->
      Typed ctx t TmStar
  *)
  .
Arguments Typed ctx t ty.
Arguments TyStar {filter} univ.
Arguments TyVarS {filter} id t.
Arguments TyAtom {filter} id.
Arguments TyPack {filter} ctx id arg arg_ty curry ty Hatom Hfora.
Arguments TyForA {filter} pf ctx ctxt ctxc ctxa arg ty body t kind Hty Hbody Hbound Hsep.
Arguments TyAppl {filter} ctx ctxf ctxx f x arg ty body substituted Hf Hx Hcat Hsubst.

Definition Typed := TypedWith MaybeConsKV.
Arguments Typed/ ctx t ty.

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
  Typed [] polymorphic_identity_fn polymorphic_identity_ty.
Proof.
  simpl. eapply TyForA.
  - (* typing `TmStar` *)
    apply TyStar.
  - (* typing the body *)
    eapply TyForA.
    + (* typing `TmVarS "t"` *)
      apply TyVarS.
    + (* typing `TmVarS "x" : TmVarS "t"` *)
      apply TyVarS.
    + (* dealing with bound variables *)
      apply MaybeConsKVCons.
    + (* partitioning the contexts used to type the type and the body *)
      apply PartitionKVMove; [| | | constructor]; intro C; destruct C as [].
    + (* concatenating the contexts used to type the type and the body *)
      simpl. reflexivity.
  - (* deadling with bound variables *)
    apply MaybeConsKVCons.
  - (* partitioning the contexts used to type the type and the body *)
    apply PartitionKVDone.
  - (* concatenating the contexts used to type the type and the body *)
    reflexivity.
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
  Typed ctx fx Y.
Proof. repeat econstructor. Qed.

(* Almost exactly like the above, but trying to use `x` twice (f : X -> X -> Y). Successfully rejected. *)
Example type_prevents_reuse : ~exists t,
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X (TmForA None X Y)) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fxx := TmAppl (TmAppl f x) x in
  Typed ctx fxx t.
Proof.
  (* In all cases, we have to use the concatenation hypothesis to show that we can't use `x` twice. *)
  intros [t C]. simpl in *.
  remember [
    ("f"%string, TmForA None (TmVarS "X") (TmForA None (TmVarS "X") (TmVarS "Y")));
    ("x"%string, TmVarS "X")] as ctx eqn:Ec. generalize dependent Ec.
  remember (TmAppl (TmAppl (TmVarS "f") (TmVarS "x")) (TmVarS "x")) as ty eqn:Et. generalize dependent Et.
  remember MaybeConsKV as filter eqn:Ef. generalize dependent Ef.
  induction C; intros; subst; simpl in *; try discriminate. invert Et. clear IHC1 IHC2.
  invert C2. destruct ctxf; invert Ec. destruct ctxf; invert H2; [| destruct ctxf; discriminate H3].
  invert C1. invert H2. invert H5. invert H3.
Qed.

(* ...But the above becomes perfectly okay if we add exchange and contraction, i.e., a heap: *)
Example type_contraction_allows_reuse :
  let f := TmVarS "f"%string in
  let x := TmVarS "x"%string in
  let X := TmVarS "X"%string in
  let Y := TmVarS "Y"%string in
  let tf := ("f"%string, TmForA None X (TmForA None X Y)) in
  let tx := ("x"%string, X) in
  let ctx := [tf; tx] in
  let fxx := TmAppl (TmAppl f x) x in
  TypedWith WhereverKV ctx fxx Y.
Proof.
  simpl. eapply TyAppl.
  - eapply TyAppl.
    + apply TyVarS.
    + apply TyVarS.
    + reflexivity.
    + Print MaybeSubst.

  econstructor; [| constructor | shelve | shelve].
  econstructor; [| constructor | shelve | shelve].
  constructor. Unshelve. 10:{ reflexivity. } 4:{ simpl. f_equal. reflexivity. } admit. admit. admit. admit. admit.

  eapply (TyExtn exchange). { right. left. reflexivity. } shelve. (* let Coq come up with the permutation for us *)
  eapply (TyExtn contraction). { left. reflexivity. } shelve.
  eapply (TyExtn exchange). { right. left. reflexivity. } shelve.
  repeat econstructor. (* this does a ridiculous amount of work for us then boxes it up so it doesn't look like it *)
  Unshelve. shelve. apply perm_swap. shelve. constructor.
  eapply perm_trans. apply perm_skip. apply perm_swap. apply perm_swap.
Qed.

(* NOTE: If we can type all functions s.t. output type represents only actual possible outputs,
   then we should be able to prove that all arrow types have an input type size
   greater than or equal to its output type size!
   Dizzying implications in terms of what a program has to start with--TODO: figure this out.
   This might be a crucial lemma in proving type safety (since a void output implies void input)! *)

Lemma maybe_cons_fst : forall {A B} f s li post,
  @MaybeConsKV A B s f            li           post ->
  @MaybeCons   A   s     (map fst li) (map fst post).
Proof. intros. induction H; constructor; assumption. Qed.

Lemma wherever_fst : forall {A B} f s li post,
  @WhereverKV A B s f            li           post ->
  @Wherever   A   s     (map fst li) (map fst post).
Proof. intros. induction H; constructor; assumption. Qed.

Lemma partition_kv_fst : forall {K V} pf hi lo,
  @PartitionKV K V pf hi lo ->
  Partition (map fst pf) (map fst hi) (map fst lo).
Proof.
  intros. induction H; simpl in *; repeat rewrite map_distr. { constructor. }
  - apply PartitionCpLo; [| assumption]. eapply find_kv_in_fst. apply H.
  - apply PartitionCpPf; [assumption | | | assumption]; eapply find_kv_in_fst; [apply H0 | apply H1].
  - apply PartitionMove; assumption.
Qed.

(* If a term `t` is typed in a context, then
 * that context has EXACTLY `fv t`, in order.
 * Fantastic that we can prove something this precise! *)
Theorem typed_free_in_structural : forall ctx t ty,
  TypedWith WhereverKV [] ctx t ty -> FreeInWith Wherever t (map fst ctx).
Proof.
  intros. remember [] as extn eqn:Ex. generalize dependent Ex. remember WhereverKV as filter eqn:Ef. generalize dependent Ef.
  induction H; intros; subst; simpl in *; try solve [constructor]; try contradiction H;
  repeat specialize (IHTypedWith eq_refl); repeat specialize (IHTypedWith1 eq_refl); repeat specialize (IHTypedWith2 eq_refl).
  - invert IHTypedWith. econstructor; [apply H4 | apply H5 | apply H7 | apply H9 | apply H10].
  - econstructor; [apply IHTypedWith1 | apply IHTypedWith2 |
      eapply (partition_map_fst _ _ _ _ eqb_spec fst_cmp_eqb) |
      rewrite map_distr; f_equal |
      destruct arg; [eapply wherever_fst; apply H1 | subst; reflexivity]].
    rewrite (map_fst_partition_pf _ _ _ _ fst_cmp_eqb).
    symmetry. apply (reflect_partition_pf _ _ _ _ eqb_spec).
    apply partition_kv_fst. assumption.
  - rewrite map_distr; econstructor; [apply IHTypedWith1 | apply IHTypedWith2 | reflexivity].
Qed.

(* If a term `t` is typed in a context, then
 * that context has EXACTLY `fv t`, in order.
 * Fantastic that we can prove something this precise! *)
Theorem typed_free_in : forall ctx t ty,
  Typed ctx t ty -> FreeIn t (map fst ctx).
Proof.
  intros. simpl in *. remember [] as extn eqn:Ex. generalize dependent Ex.
  remember MaybeConsKV as filter eqn:Ef. generalize dependent Ef.
  induction H; intros; subst; simpl in *; try solve [constructor]; try contradiction H.
  - specialize (IHTypedWith eq_refl eq_refl). invert IHTypedWith.
    econstructor; [apply H4 | apply H5 | apply H7 | assumption | assumption].
  - specialize (IHTypedWith2 eq_refl eq_refl). econstructor.
    + eapply typed_free_in_structural. apply H.
    + apply IHTypedWith2.
    + eapply partition_kv_fst. apply H2.
    + apply map_distr.
    + destruct arg. { eapply maybe_cons_fst. apply H1. } subst. reflexivity.
  - specialize (IHTypedWith1 eq_refl eq_refl). specialize (IHTypedWith2 eq_refl eq_refl). rewrite map_distr.
    econstructor; [apply IHTypedWith1 | apply IHTypedWith2 | reflexivity].
Qed.

Theorem fv_not_typed : forall t,
  fv t <> [] -> ~exists ty, Typed [] t ty.
Proof.
  intros t H [ty C]. destruct (fv t) eqn:Ef. { apply H. reflexivity. } clear H.
  eapply reflect_fv in Ef; [| intros; apply maybe_cons_remove_if_head]. apply typed_free_in in C.
  eapply reflect_fv in C ; [| intros; apply maybe_cons_remove_if_head].
  eapply reflect_fv in Ef; [| intros; apply maybe_cons_remove_if_head].
  rewrite Ef in C. discriminate C.
Qed.

Theorem typed_fv : forall ctx t ty,
  Typed ctx t ty ->
  fv t = map fst ctx.
Proof. intros. eapply reflect_fv. { intros. apply maybe_cons_remove_if_head. } eapply typed_free_in. apply H. Qed.

(*
TODO: This is damn fucking hard to prove.
Theorem fv_type_not_typed : forall ty,
  fv_with remove_all ty <> [] -> ~exists t, Typed [] t ty.
Proof.
  intros ty H [t C]. simpl in *. generalize dependent H.
  remember MaybeConsKV as filter eqn:Ef. generalize dependent Ef.
  remember [] as extn eqn:Ee. generalize dependent Ee.
  remember [] as ctx eqn:Ec. generalize dependent Ec.
  induction C; intros; subst; simpl in *; try (contradiction H; reflexivity); [discriminate Ec | | |];
  [destruct pf; destruct ctxc; invert Ec | destruct pf; destruct ctxc; invert Ec | destruct ctxf; destruct ctxx; invert Ec];
  rewrite slow_down in *; [invert H1; [| invert H2 | invert H4] | invert H0; [| invert H1 | invert H3] |];
  repeat specialize (IHC1 eq_refl); repeat specialize (IHC2 eq_refl); repeat rewrite slow_down in *. 3: {
    destruct arg.
    - admit.
    - Search partition_pf.
  
  ; destruct arg; subst.
  - admit.
  - apply typed_free_in_structural in C1. simpl in *.

  induction C; intros; subst; simpl in *; try contradiction; try discriminate; repeat rewrite slow_down in *; simpl in *;
  [destruct pf; destruct ctxc; invert Ec | destruct pf; destruct ctxc; invert Ec | destruct ctxf; destruct ctxx; invert Ec].
  - invert H1; [| invert H2 | invert H4]. destruct arg.
    + apply typed_free_in_structural in C1. eapply reflect_fv_structural in C1. rewrite C1 in *. simpl in *.
      destruct (fv_with remove_if_head t) eqn:Ef. { apply H3. reflexivity. } destruct ctxa.
      * apply IHC2; try reflexivity. intro C. discriminate C.
      * invert H0. invert C2; try solve [inversion H].
      apply IHC2; try reflexivity; [| intro C; discriminate C].
    + subst. apply typed_free_in_structural in C1. simpl in *.
      eapply reflect_fv_structural in C1. rewrite C1 in *. simpl in *. apply IHC2; try reflexivity. assumption.
  - 

  ; subst; simpl in *; repeat rewrite slow_down in *;
  [admit | admit | admit | destruct H].
  admit. admit. admit.
  - destruct pf; destruct ctxc; invert Ec. specialize (IHC1 eq_refl). specialize (IHC2 eq_refl).
    destruct arg; simpl in *; subst. admit.
    + invert H1. admit.
    assert (A := typed_free_in _ _ _ C1). apply reflect_fv in A. simpl in *. repeat rewrite A in *. simpl in *.
    destruct arg; [| subst; apply IHC2; try reflexivity; assumption]. destruct (mint ty).
    + 

    destruct (mint ty).
    admit. ; [| apply (IHC2 eq_refl H1)]. clear IHC2.
    destruct (fv_slow t) as [| hd tl] eqn:Et; [contradiction |].
    induction H0; invert C2.
Abort.

(*****)

Fixpoint delete n {T} (li : list T) :=
  match li with
  | [] => None
  | hd :: tl =>
      match n with
      | O => Some tl
      | S n' => option_map (cons hd) (delete n' tl)
      end
  end.

Lemma delete_exact : forall {T} la (x : T) lb,
  delete (Datatypes.length la) (la ++ x :: lb) = Some (la ++ lb).
Proof. intros T la. induction la; intros; simpl in *; [| rewrite IHla]; reflexivity. Qed.

Theorem grand_unified_subst_preserves_typing : forall ctx t T i x,
  Typed ctx t T ->
  nth_error ctx i = Some (x, t) ->
  exists f, (
    nth_error (grand_unified_subst t) i = Some (x, f) /\
    exists ctx', (
      delete i ctx = Some ctx' /\
      forall y,
      Typed [] y t ->
      Typed ctx' (f y) T)).
Proof.
  intros ctx t T i x Ht Hc. apply nth_error_split in Hc as [ctxa [ctxb [Hc Hl]]]. subst.
  assert (Hf := typed_fv _ _ _ Ht). assert (Hg := grand_unified_subst_exactly_fv t).
  destruct (nth_error (grand_unified_subst t) (Datatypes.length ctxa)) as [[y f] |] eqn:En. 2: {
    rewrite (nth_error_nth' _ ("doesn't matter"%string, fun x => x)) in En. { discriminate En. }
    assert (A : Datatypes.length (grand_unified_subst t) = Datatypes.length (ctxa ++ (x, t) :: ctxb)). {
      rewrite Hf in Hg. eapply f_equal in Hg. repeat rewrite map_length in Hg. symmetry. assumption. }
    rewrite app_length in A. rewrite A. simpl. apply Nat.lt_add_pos_r. apply Nat.lt_0_succ. }
  apply nth_error_split in En as [gusa [gusb [Eg El]]]. repeat rewrite Eg in *.
  assert (A : y = x). {
    rewrite Hf in Hg. assert (N :
      nth_error (map fst (ctxa ++ (x, t) :: ctxb)) (Datatypes.length ctxa) =
      nth_error (map fst (gusa ++ (y, f) :: gusb)) (Datatypes.length gusa)
    ). { f_equal. assumption. symmetry. assumption. } repeat rewrite nth_error_map in N.
    rewrite nth_error_app2 in N; [| constructor]. rewrite nth_error_app2 in N; [| constructor].
    repeat rewrite Nat.sub_diag in N. simpl in *. invert N. reflexivity. } subst.
  exists f. split. { reflexivity. } exists (ctxa ++ ctxb). split. { apply delete_exact. } intros; simpl in *.
  rewrite Hf in Hg. clear Hf.
  (*********************************************************************************************************)
  generalize dependent f. generalize dependent gusa. generalize dependent gusb. generalize dependent y.
  remember (ctxa ++ (x, t) :: ctxb) as ctx eqn:Ectx.
  generalize dependent ctxa. generalize dependent ctxb. generalize dependent x.
  induction Ht; intros; subst; simpl in *; try (destruct gusa; discriminate).
  - destruct gusa; [| destruct gusa]; invert Hg. destruct gusb; invert H2. invert Eg.
    destruct ctxa; invert El. invert Ectx. assumption.
  - admit.
  - admit.
  - admit.
  - clear IHHt1 IHHt2. invert H1.
  - clear IHHt1 IHHt2. invert H1.
    + destruct ctxf; destruct ctxx; invert H3. simpl in *. invert H.

  generalize dependent y. generalize dependent gusa. generalize dependent gusb. generalize dependent f.
  generalize dependent ctxb. generalize dependent ctxa. generalize dependent x. generalize dependent T.
  induction t; intros; try (destruct gusa; discriminate Eg); simpl in *.
  - destruct gusa; [| destruct gusa]; invert Eg. destruct ctxa; [| discriminate El]. destruct ctxb; invert Hf.
    simpl in *. clear Hg El. invert Ht. assumption.
  - invert Ht. generalize dependent arg. generalize dependent t1. generalize dependent IHt2. generalize dependent x.
    generalize dependent ctxa. generalize dependent ctxb. generalize dependent t. generalize dependent f.
    generalize dependent gusb. generalize dependent gusa. generalize dependent y. generalize dependent ctxt.
    generalize dependent ctxc. generalize dependent kind. induction H9; intros; simpl in *; subst; simpl in *.
    + clear IHt2. (* contradictory *) destruct arg; invert H7. simpl in *. repeat rewrite app_nil_r in *. subst.
      eapply IHt1.
      clear IHt1 IHt2 Hf Eg Hg.

  - invert Ht. assert (A := Nat.leb_spec0 (Datatypes.length ctxt) (Datatypes.length ctxa)). destruct A.
    + generalize dependent id. generalize dependent arg. generalize dependent t1. generalize dependent t2.
      generalize dependent x. generalize dependent ctxt. generalize dependent ctxb. generalize dependent t.
      generalize dependent f. generalize dependent gusb. generalize dependent gusa. generalize dependent y.
      generalize dependent ctxc. generalize dependent kind. induction ctxa; intros; subst; simpl in *.
      * destruct ctxt; invert l. destruct gusa; invert El.
        assert (A := typed_fv _ _ _ H5). simpl in A. rewrite A in *. clear IHt1. (* contradictory *)
        assert (B := A). rewrite grand_unified_subst_exactly_fv in B. destruct (grand_unified_subst t1); invert B.
        simpl in *. subst. simpl in *.
        destruct arg as [arg |]; simpl in *. 2: {
          destruct (grand_unified_subst t2) eqn:E2; invert Eg. destruct p. invert H1.
          repeat rewrite Hf in *. invert Hg. repeat rewrite H1 in *.
          econstructor; [apply H5 | | reflexivity |].
          - eapply (IHt2 _ _ []); clear IHt2; simpl in *; [| f_equal; symmetry; assumption | rewrite app_nil_l; reflexivity | simpl; f_equal | reflexivity |].
            + admit.
            + admit.
            + reflexivity.
          repeat rewrite H1 in *. eapply (IHt2 _ _ []); simpl in *; [| f_equal; symmetry; apply H1 | | | |].
          - admit.
          - f_equal. symmetry. apply H1.
        }
        clear IHt1 IHt2. clear Hf Eg Hg. eapply (IHt1 _ _ []); clear IHt1 IHt2; simpl in *.
        clear Hf Eg Hg.
  - invert Ht. destruct arg as [arg |]. 2: {
      destruct (Datatypes.length ctxt <=? Datatypes.length ctxa) eqn:Ec.
      rewrite Hg in Hf. clear IHt1 IHt2. Hf Eg Hg. invert H.
    }
Qed.



















































(* Look up a value by key and remove it from a key-value list. *)
Fixpoint yoink {T} s (li : list (string * T)) :=
  match li with
  | [] => None
  | (k, v) :: tl => if eqb s k then Some (v, tl) else
      let f : (T * (list (string * T))) -> _ := fun x =>
        let (out, etc) := x in (out, (k, v) :: etc) in
      option_map f (yoink s tl)
  end.

Example yoink_12345 :
  yoink "c" [("a", 1); ("b", 2); ("c", 3); ("d", 4); ("e", 5)]%string =
  Some (3, [("a", 1); ("b", 2); ("d", 4); ("e", 5)]%string).
Proof. reflexivity. Qed.

Theorem yoink_app : forall {T} s a b out etc,
  @yoink T s (a ++ b) = Some (out, etc) ->
  ((exists pre, etc = pre ++ b /\ yoink s a = Some (out, pre)) \/
  (exists post, etc = a ++ post /\ yoink s a = None /\ yoink s b = Some (out, post))).
Proof.
  intros T s a. generalize dependent s. induction a; intros; simpl in *; subst.
  - right. eexists. repeat split; assumption.
  - destruct a. destruct (eqb s s0) eqn:E.
    + apply eqb_eq in E. invert H. left. eexists. repeat split.
    + destruct (yoink s (a0 ++ b)) eqn:Ey; try discriminate H. destruct p. invert H.
      apply IHa in Ey. destruct Ey as [[pre [H1 H2]] | [post [H1 [H2 H3]]]]; subst; simpl in *.
      * left. rewrite H2. eexists; repeat split; try reflexivity.
      * right. rewrite H2. rewrite H3. eexists; repeat split.
Qed.

Fixpoint yank {T} i (li : list T) :=
  match li with
  | [] => None
  | hd :: tl =>
      match i with
      | O => Some (hd, tl)
      | S j => 
          let f := fun x : _ * _ => let (out, etc) := x in (out, hd :: etc) in
          option_map f (yank j tl)
      end
  end.

Fixpoint checked_sub amt from :=
  match from, amt with
  | _, O => Some from
  | S f, S a => checked_sub a f
  | _, _ => None
  end.

Example checked_sub_3_5 : checked_sub 3 5 = Some 2. Proof. reflexivity. Qed.
Example checked_sub_5_3 : checked_sub 5 3 = None. Proof. reflexivity. Qed.

Theorem checked_sub_le : forall amt from,
  checked_sub amt from <> None <-> amt <= from.
Proof.
  induction amt; intros; simpl in *.
  - split; intros. { apply le_0_n. } intro C. destruct from; discriminate C.
  - split; intros; destruct from; try contradiction. { apply le_n_S. apply IHamt. assumption. }
    { invert H. } apply le_S_n in H. apply IHamt. assumption.
Qed.

Theorem checked_sub_sub : forall amt from out,
  checked_sub amt from = out ->
  from - amt = match out with Some x => x | None => O end.
Proof.
  induction amt; intros; simpl in *. { destruct from; invert H; reflexivity. }
  destruct from; subst; simpl in *. { reflexivity. } apply IHamt. reflexivity.
Qed.

Theorem yank_app : forall {T} i a b,
  @yank T i (a ++ b) =
  match checked_sub (Datatypes.length a) i with
  | None =>
      let f : _ * _ -> _ := fun x => let (out, etc) := x in (out, etc ++ b) in
      option_map f (yank i a)
  | Some past_a =>
      let f : _ * _ -> _ := fun x => let (out, etc) := x in (out, a ++ etc) in
      option_map f (yank past_a b)
  end.
Proof.
  intros T i a. generalize dependent i. induction a; intros; simpl in *.
  - destruct i; destruct b; simpl; try reflexivity.
    destruct (yank i b); simpl; try reflexivity. destruct p. reflexivity.
  - destruct i; simpl in *. { reflexivity. } rewrite IHa. clear IHa.
    destruct (checked_sub (Datatypes.length a0) i); simpl in *.
    + destruct (yank n b); simpl; try reflexivity. destruct p. reflexivity.
    + destruct (yank i a0); try reflexivity. destruct p. reflexivity.
Qed.

Lemma nth_error_short_circuit : forall {T} i a b out,
  @nth_error T a i = Some out ->
  nth_error (a ++ b) i = Some out.
Proof.
  intros T i a. generalize dependent i. induction a; intros; simpl in *. { destruct i; discriminate H. }
  destruct i; simpl in *. { invert H. reflexivity. } apply IHa. assumption.
Qed.

Lemma nth_error_smap : forall f li i,
  nth_error (smap f li) i = option_map (fun pair : _ * _ => let (a, b) := pair in (a, f b)) (nth_error li i).
Proof.
  intros f li. generalize dependent f. induction li; intros; simpl in *. { destruct i; reflexivity. }
  destruct a. destruct i; simpl in *. { reflexivity. } apply IHli.
Qed.

Theorem grand_unified_subst_preserves_typing : forall ctx t ty,
  Typed ctx t ty ->
  forall i s st ctx',
  yank i ctx = Some ((s, st), ctx') ->
  exists f,
  nth_error (grand_unified_subst t) i = Some (s, f) /\
  forall y,
  Typed [] y st ->
  Typed ctx' (f y) ty.
Proof.
  intros ctx t ty H. induction H; intros; simpl in *; subst.
  - destruct i; [| destruct i; discriminate]. invert H. eexists. repeat split. intros. assumption.
  - destruct i; discriminate H.
  - rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:Ec;
    [destruct (yank n ctxc) eqn:Ey | destruct (yank i ctxt) eqn:Ey]; try discriminate H3; destruct p; invert H3.
    + admit.
    + destruct arg.
      * admit.
      * eapply IHTyped1 in Ey as [f [E1 E2]]. clear IHTyped1; clear IHTyped2.
        erewrite nth_error_short_circuit; [| rewrite nth_error_smap; rewrite E1; reflexivity].
        eexists; repeat split. intros. apply E2 in H1. simpl. eapply TyPack. econstructor. assumption.
        rewrite nth_error_smap. rewrite E1; reflexivity.

    + assert (A : checked_sub (Datatypes.length ctxt) i <> None). { rewrite Ec. intro C. discriminate C. }
      apply checked_sub_le in A. destruct arg.
      * rewrite nth_error_app2; rewrite smap_len; assert (F := typed_fv _ _ _ H);
        rewrite grand_unified_subst_exactly_fv in F; eassert (L := f_equal _ F);
        repeat rewrite map_length in L; rewrite L; try assumption.
        clear IHTyped1; clear IHTyped2. eexists. split.
        -- rewrite (checked_sub_sub _ _ _ Ec).
  - destruct arg.
    + clear IHTyped1; clear IHTyped2.

    + admit.
    + rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:Ec.
      * destruct (yank n ctxc) eqn:Ey; try discriminate H3. destruct p. destruct p. invert H3.
        apply IHTyped2 in Ey as [f [E1 E2]].
        assert (A : checked_sub (Datatypes.length ctxt) i <> None). { rewrite Ec. intro C. discriminate C. }
        apply checked_sub_le in A. eexists. rewrite nth_error_app2; [|
          rewrite smap_len; apply typed_fv in H; rewrite grand_unified_subst_exactly_fv in H;
          eapply f_equal in H; repeat rewrite map_length in H; rewrite H; assumption].
        split. admit. intros. simpl in *. clear IHTyped1; clear IHTyped2.

    + rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i). clear IHTyped1; clear IHTyped2.
  - rewrite yank_app in H3. destruct (checked_sub (Datatypes.length ctxt) i) eqn:E.
    + destruct (yank n ctxc) eqn:Ey; try discriminate H3. clear IHTyped1; clear IHTyped2. destruct p. invert H3. destruct arg.
      * admit.
      * assert (A := checked_sub_le (Datatypes.length ctxt) i).
      * apply checked_sub_le in E. Search nth_error. simpl in *.

  - clear IHTyped1; clear IHTyped2. assert (A := typed_fv _ _ _ H). rewrite grand_unified_subst_exactly_fv in A. destruct arg.
    + admit.
    + 

  intros ctx. induction ctx; intros; simpl in *. { destruct i; discriminate H0. }
  Search fv.
  assert (A := typed_fv _ _ _ H).
  rewrite grand_unified_subst_exactly_fv in A.
  destruct a.
  apply grand_unified_subst_exactly_fv 
  Search grand_unified_subst.
  apply IHctx.
Qed.

Theorem grand_unified_subst_preserves_typing : forall ctx t ty,
  (* A mouthful: if you substitute a variable in context with something of its assigned type,
   * and if you then remove that variable from the context,
   * then the type of the whole expression after substitution doesn't change. *)
  Typed ctx t ty ->
  forall x xt ctx',
  yoink x ctx = Some (xt, ctx') ->
  forall y,
  Typed [] y xt ->
  exists s,
  subst x y t = Some s /\ Typed ctx' s ty.
Proof.
  intros ctx t ty H. induction H; intros; simpl in *; subst; try discriminate.
  - destruct (eqb x id) eqn:E; invert H. apply eqb_eq in E. subst. simpl in *.
    eexists. split. { reflexivity. } assumption.
  - apply yoink_app in H3. destruct H3 as [[pre [E1 E2]] | [post [E1 [E2 E3]]]].
    + eapply IHTyped1 in E2 as [s [E2 E3]]. clear IHTyped1; clear IHTyped2. subst. destruct arg.
    + clear IHTyped1; clear IHTyped2. simpl in *.
Qed.

Theorem subst_preserves_typing : forall x y t ty s,
  Typed [] t ty ->
  subst x y t = Some s ->
  Typed [] s ty.
Proof.
  intros x y t. generalize dependent y. generalize dependent x.
  induction t; intros; simpl in *; try discriminate.
  - apply typed_fv in H. discriminate H.
  - invert H. destruct ctxt; destruct ctxc; invert H9. clear H0. destruct arg.
    + admit.
    + eapply IHt2.

  - assert (A := fv_not_typed (TmVarS id)). contradiction A. { intro C. discriminate C. } exists ty. assumption.
  - clear H0. induction H.
    + eapply IHt2.
  - destruct arg.
    + clear H0. invert H. simpl in *.

  - destruct (eqb x id) eqn:E; invert H0. apply eqb_eq in E. subst. induction H.
Qed.
*)
*)
