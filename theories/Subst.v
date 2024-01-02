From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  FreeVariables
  Invert
  Partition
  SplitRemove
  StructuralFreeVariables
  StructuralHole
  StructuralSubst
  Terms.

Fixpoint subst_hole_acc acc x t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      (SHoleTerm t, acc)
  | TmVarS z =>
      if eqb z x then
        match acc with
        (* no shadowing *)
        | Some O => (SHoleHere, None)
        (* shadowed *)
        | Some (S n) => (SHoleTerm t, Some n)
        (* already used *)
        | None => (SHoleTerm t, None)
        end
      else
        (SHoleTerm t, acc)
  | TmPack id arg ty curry =>
      let (scurry, ac1) := subst_hole_acc (if eq_opt arg (Some x) then option_map S acc else acc) x curry in
      (SHolePack id arg (structural_subst_hole x ty) scurry, ac1)
  | TmForA arg ty body =>
      let (sbody, ac1) := subst_hole_acc (if eq_opt arg (Some x) then option_map S acc else acc) x body in
      (SHoleForA arg (structural_subst_hole x ty) sbody, ac1)
  | TmAppl f z =>
      let (sf, ac1) := subst_hole_acc acc x f in
      let (sz, ac2) := subst_hole_acc ac1 x z in
      (SHoleAppl sf sz, ac2)
  end.
Definition subst_hole := subst_hole_acc (Some O).
Arguments subst_hole/ x t.
Definition subst x y t := sfill (fst (subst_hole x t)) y.
Arguments subst/ x y t.

Example subst_simple_f : forall f x, (* note that we don't require `f <> x` *)
  subst f TmVoid (TmAppl (TmVarS f) (TmVarS x)) = TmAppl TmVoid (TmVarS x).
Proof. intros. simpl. rewrite eqb_refl. destruct (eqb x f); reflexivity. Qed.

Example subst_simple_x : forall f x, f <> x ->
  subst x TmVoid (TmAppl (TmVarS f) (TmVarS x)) = TmAppl (TmVarS f) TmVoid.
Proof. intros. simpl. apply eqb_neq in H. rewrite H. rewrite eqb_refl. reflexivity. Qed.

Example subst_lambda_t : forall t x, x <> t ->
  subst t TmVoid (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x)).
Proof. intros. simpl. apply eqb_neq in H. rewrite H. simpl. rewrite eqb_refl. reflexivity. Qed.

Example subst_lambda_x : forall t x, t <> x ->
  subst x TmVoid (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) TmVoid). (* Note that we ignore the first `x`! *)
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. reflexivity. Qed.

Example subst_lambda_x_l : forall t x, t <> x ->
  subst x TmVoid (TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) (TmVarS x)) (TmVarS x))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmAppl (TmVarS x) TmVoid) (TmVarS x)).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. reflexivity. Qed.

Example subst_lambda_x_r : forall t x, t <> x ->
  subst x TmVoid (TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl (TmVarS x) (TmVarS x)))) =
  TmForA (Some x) (TmVarS t) (TmAppl (TmVarS x) (TmAppl TmVoid (TmVarS x))).
Proof. intros. simpl. rewrite eqb_refl. apply eqb_neq in H. rewrite H. reflexivity. Qed.

Theorem subst_fv : forall x y t,
  fv (subst x y t) =
  match splitrm (eqb x) (fv t) with
  | None => fv t
  | Some (pre, post) => pre ++ fv y ++ post
  end.
Proof.
  intros. rewrite splitrm_fast_slow. simpl in *. generalize dependent x. generalize dependent y.
  induction t; intros; simpl in *; try reflexivity; repeat rewrite slow_down in *.
  - destruct (eqb_spec x id). { subst. rewrite eqb_refl. rewrite app_nil_r. reflexivity. }
    apply eqb_neq in n. rewrite eqb_sym in n. rewrite n. reflexivity.
  - destruct arg as [arg |]; simpl in *.
    + admit.
    + destruct (subst_hole_acc (Some 0) x t2) as [scurry ac1] eqn:E. simpl in *. rewrite slow_down.
      rewrite <- splitrm_fast_slow. rewrite splitrm_app. repeat rewrite splitrm_fast_slow.
      clear IHt1 IHt2.
Qed.

Fixpoint count_slow {T} (f : T -> bool) li :=
  match li with
  | [] => O
  | hd :: tl => let n := count_slow f tl in if f hd then S n else n
  end.

Fixpoint count_fast acc {T} (f : T -> bool) li :=
  match li with
  | [] => acc
  | hd :: tl => count_fast (if f hd then S acc else acc) f tl
  end.
Definition count := @count_fast O.
Arguments count/ {T} f li.

Lemma count_fast_acc : forall acc {T} f li,
  count_fast (S acc) f li = S (@count_fast acc T f li).
Proof.
  intros. generalize dependent acc. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. } destruct (f a); apply IHli.
Qed.

Theorem count_fast_slow : forall {T} f li,
  count f li = @count_slow T f li.
Proof.
  intros. generalize dependent f. induction li; intros; simpl in *. { reflexivity. }
  destruct (f a); [rewrite count_fast_acc; f_equal |]; apply IHli.
Qed.

Theorem subst_fv : forall t x y n,
  count (eqb x) (fv t) = S n ->
  count (eqb x) (fv (subst x y t)) = n + count (eqb x) (fv y).
Proof.
  intros. simpl in *. repeat rewrite count_fast_slow in *. generalize dependent x. generalize dependent y.
  generalize dependent n. induction t; intros; try discriminate H.
  - simpl in *. destruct (eqb_spec x id); invert H. rewrite eqb_refl. reflexivity.
  - simpl in *. destruct (subst_hole_acc (if eq_opt arg (Some x) then Some 1 else Some O) x t2) as [scurry ac1] eqn:E.
    simpl in *. rewrite slow_down in *. destruct arg; simpl in *.
    + admit.
    + Print partition_pf_slow. 
Qed.

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
