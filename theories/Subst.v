From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  FreeVariables
  FstCmp
  Hole
  Invert
  Partition
  PartitionKV
  StructuralFreeVariables
  StructuralSubst
  Terms.

Definition remove_key_if_head {T} x (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, f) :: tl => if eqb x s then tl else li
  end.

Lemma remove_if_head_key_eq : forall {T} x (li : list (string * T)),
  map fst (remove_key_if_head x li) = remove_if_head x (map fst li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. destruct (eqb x s) eqn:E. { reflexivity. } simpl. reflexivity.
Qed.

Theorem incl_remove_key : forall {T} x (li : list (string * T)),
  incl (remove_key_all x li) (remove_key_if_head x li).
Proof.
  intros. unfold incl. generalize dependent x. induction li; intros; simpl in *. { destruct H. }
  destruct a. destruct a0. destruct (eqb_spec x s).
  - subst. apply IHli in H. unfold remove_key_if_head in H. destruct li. { destruct H. }
    destruct p. destruct (eqb s s1); [right |]; assumption.
  - destruct H. { invert H. left. reflexivity. }
    apply IHli in H. unfold remove_key_if_head in H. destruct li. { destruct H. }
    destruct p. destruct (eqb x s1); [right |]; right; assumption.
Qed.

(* Ludicrous that this is the easiest correct definition to write.
 * Generates substitution functions for every free variable at once. *)
Fixpoint grand_unified_subst t : option (list (string * hole)) :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      Some []
  | TmVarS s =>
      Some [(s, HoleHere)]
  | TmPack id arg ty curry =>
      match grand_unified_subst curry with
      | None => None
      | Some recursed =>
        let lo := smap (HolePackCurry id arg ty) (
          match arg with
          | None => recursed
          | Some a => remove_key_if_head a recursed
          end) in
        let hi := smap (fun h => HolePackTy id arg h curry) (structural_grand_unified_subst ty) in
        option_map (fun li => li ++ lo) (partition_kv_pf eqb eq_hole hi lo)
      end
  | TmForA arg ty body =>
      match grand_unified_subst body with
      | None => None
      | Some recursed =>
        let lo := smap (HoleForABody arg ty) (
          match arg with
          | None => recursed
          | Some a => remove_key_if_head a recursed
          end) in
        let hi := smap (fun h => HoleForATy arg h body) (structural_grand_unified_subst ty) in
        option_map (fun li => li ++ lo) (partition_kv_pf eqb eq_hole hi lo)
      end
  | TmAppl f x =>
      match grand_unified_subst f, grand_unified_subst x with
      | Some sf, Some sx => Some (smap (fun h => HoleApplF h x) sf ++ smap (HoleApplX f) sx)
      | _, _ => None
      end
  end.

Definition subst x y t :=
  match grand_unified_subst t with
  | None => None
  | Some s => option_map (fun f => fill f y) (pair_lookup x s)
  end.
Arguments subst x y t/.

Example subst_simple : forall f x,
  subst f TmVoid (TmAppl (TmVarS f) (TmVarS x)) = Some (TmAppl TmVoid (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example grand_unified_subst_simple :
  grand_unified_subst (TmAppl (TmVarS "f"%string) (TmVarS "x"%string)) = Some [
    ("f", HoleApplF HoleHere (TmVarS "x"));
    ("x", HoleApplX (TmVarS "f") HoleHere)]%string.
Proof. reflexivity. Qed.

Example grand_unified_subst_lambda :
  grand_unified_subst (TmForA (Some "x") (TmVarS "T") (TmAppl (TmVarS "x") (TmVarS "x")))%string = Some [
    ("T", HoleForATy (Some "x") HoleHere (TmAppl (TmVarS "x") (TmVarS "x")));
    (* ignore the first `x`, since it's bound, then *)
    ("x", HoleForABody (Some "x") (TmVarS "T") (HoleApplX (TmVarS "x") HoleHere))]%string.
Proof. reflexivity. Qed.

Lemma fst_cmp_eqb : forall {T} a a' b b',
  @fst_cmp T T (a, b) (a', b') = eqb a a'.
Proof. reflexivity. Qed.

Theorem grand_unified_subst_fv : forall t s,
  grand_unified_subst t = Some s ->
  fv t = map fst s.
Proof.
  induction t; intros; simpl in *; try solve [invert H; reflexivity]; repeat rewrite slow_down in *;
  repeat rewrite structural_grand_unified_subst_fv in *.
  - destruct (grand_unified_subst t2) as [s2 |] eqn:Es2; [| discriminate H].
    specialize (IHt2 _ eq_refl). repeat rewrite IHt2 in *. rewrite slow_down_kv in H.
    destruct (partition_kv_pf_slow eqb eq_hole
      (smap (fun h : hole => HolePackTy id arg h t2) (structural_grand_unified_subst t1))
      (smap (HolePackCurry id arg t1) match arg with Some a => remove_key_if_head a s2 | None => s2 end)
    ) eqn:Ep; invert H; simpl in *. rewrite <- partition_kv_pf_fast_slow in Ep. eapply partition_kv_pf_works in Ep.
    Search (PartitionKV _ _ _ -> _).
    destruct arg. 2: {
      rewrite <- partition_pf_fast_slow. rewrite <- (map_fst_partition_pf _ _ _ _ fst_cmp_eqb).
      rewrite map_distr. rewrite map_fst_smap. f_equal. Search fst_cmp.
    Search partition_pf.
    clear H.
  rewrite map_distr; try rewrite (map_fst_partition_pf _ _ _ _ fst_cmp_eqb); repeat rewrite map_fst_smap;
  repeat rewrite IHt1; repeat rewrite IHt2; [| | reflexivity]; rewrite structural_grand_unified_subst_fv;
  (destruct arg; [| reflexivity]); repeat rewrite partition_pf_fast_slow; (destruct (grand_unified_subst t2); [reflexivity |]);
  destruct p as [v f]; simpl; destruct (eqb s v); reflexivity.
Qed.
(* WOOHOOOOOOOOOOOOOOO *)

Lemma remove_key_if_head_incl : forall {T} x (li : list (string * T)),
  incl (remove_key_if_head x li) li.
Proof.
  unfold incl. intros T x [] [a1 a2] H. { inversion H. } destruct p. simpl in H. destruct (eqb x s); [right |]; assumption.
Qed.

Theorem incl_partition_pf_fst : forall {T} hi lo,
  incl (@partition_pf_slow (string * T) fst_cmp hi lo) hi.
Proof.
  unfold incl. induction hi; intros; simpl in *. { destruct H. }
  destruct (existsb (fst_cmp a) lo) eqn:El; simpl in *. { right. apply (IHhi _ _ H). }
  destruct (existsb (fst_cmp a) hi) eqn:Eh; simpl in *. { right. apply (IHhi _ _ H). }
  destruct a as [k1 v1]. destruct a0 as [k2 v2]. destruct H; [| right; apply (IHhi _ _ H)].
  left. assumption.
Qed.

Theorem grand_unified_subst_id : forall t,
  let P := fun p : _ * _ => let (x, f) := p in fill f (TmVarS x) = t in
  Forall P (grand_unified_subst t).
Proof.
  induction t as [| | | | id arg a IHa b IHb | arg a IHa b IHb | a IHa b IHb]; simpl in *; repeat constructor; [| |
    apply Forall_app; split; apply Forall_smap; (eapply Forall_impl; [| try apply IHa; apply IHb]);
    intros; destruct a0; simpl; rewrite H; reflexivity]; repeat rewrite slow_down; destruct arg;
  apply Forall_app; (split; [eapply incl_Forall; [apply incl_partition_pf_fst |] |]);
  apply Forall_smap; try (eapply incl_Forall; [apply remove_key_if_head_incl |]);
  (eapply Forall_impl; [| try apply structural_grand_unified_subst_id; apply IHb]);
  intros; destruct a0; simpl; rewrite H; reflexivity.
Qed.

Theorem subst_id : forall x t s,
  subst x (TmVarS x) t = Some s ->
  s = t.
Proof.
  intros. unfold subst in *. destruct (pair_lookup x (grand_unified_subst t)) eqn:Ep; invert H.
  eapply pair_lookup_Forall in Ep; [| apply grand_unified_subst_id]. assumption.
Qed.

Variant DecapitateK {K V} (k : K) : list (K * V) -> list (K * V) -> Prop :=
  | DecapitateKNil :
      DecapitateK k [] []
  | DecapitateKConsEq : forall hv tl,
      DecapitateK k ((k, hv) :: tl) tl
  | DecapitateKConsNEq : forall hk hv tl,
      k <> hk ->
      DecapitateK k ((hk, hv) :: tl) ((hk, hv) :: tl)
  .

Theorem reflect_decapitate_k : forall {V} k li post,
  remove_key_if_head k li = post <-> @DecapitateK _ V k li post.
Proof.
  split; intros.
  - subst. destruct li; simpl in *. { constructor. }
    destruct p. destruct (eqb_spec k s). { subst. constructor. } constructor. assumption.
  - destruct H; simpl in *; [| rewrite eqb_refl | apply eqb_neq in H; rewrite H]; reflexivity.
Qed.

Inductive GrandUnifiedSubst : term -> list (string * hole) -> Prop :=
  | GUSVoid :
      GrandUnifiedSubst TmVoid []
  | GUSStar : forall univ,
      GrandUnifiedSubst (TmStar univ) []
  | GUSVarS : forall s,
      GrandUnifiedSubst (TmVarS s) [(s, HoleHere)]
  | GUSAtom : forall id,
      GrandUnifiedSubst (TmAtom id) []
  | GUSPack : forall id arg ty curry sty scurry scurry_orig pf s,
      GrandUnifiedSubst ty sty ->
      GrandUnifiedSubst curry scurry_orig ->
      match arg with
      | None => eq
      | Some a => DecapitateK a
      end scurry_orig scurry ->
      PartitionKV pf sty scurry ->
      s = smap (fun h => HolePackTy id arg h curry) pf ++ smap (HolePackCurry id arg ty) scurry ->
      GrandUnifiedSubst (TmPack id arg ty curry) s
  | GUSForA : forall arg ty body sty sbody sbody_orig pf s,
      GrandUnifiedSubst ty sty ->
      GrandUnifiedSubst body sbody_orig ->
      match arg with
      | None => eq
      | Some a => DecapitateK a
      end sbody_orig sbody ->
      PartitionKV pf sty sbody ->
      s = smap (fun h => HoleForATy arg h body) pf ++ smap (HoleForABody arg ty) sbody ->
      GrandUnifiedSubst (TmForA arg ty body) s
  | GUSAppl : forall f x sf sx s,
      GrandUnifiedSubst f sf ->
      GrandUnifiedSubst x sx ->
      s = smap (fun h => HoleApplF h x) sf ++ smap (HoleApplX f) sx ->
      GrandUnifiedSubst (TmAppl f x) s
  .

Theorem reflect_structural_grand_unified_subst : forall t s,
  grand_unified_subst t = s <-> GrandUnifiedSubst t s.
Proof.
  split; intros.
  - generalize dependent s. induction t; intros; subst; simpl in *; try solve [constructor]; try rewrite slow_down.
    + econstructor.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
      * shelve.
      * apply (partition_pf_works). Search (partition_pf).
      * f_equal.

    econstructor. ; try apply IHt1; try apply IHt2; try reflexivity; (destruct arg; [apply reflect_purge_k |]); reflexivity.
  - induction H; subst; simpl in *; f_equal; (destruct arg; [| subst; reflexivity]);
    apply reflect_purge_k in H1; subst; reflexivity.
Qed.
