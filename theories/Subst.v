From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  FreeVariables
  FstCmp
  Invert
  Partition
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
Fixpoint grand_unified_subst t : list (string * (term -> term)) :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [(s, fun x => x)]
  | TmPack id arg ty curry =>
      let lo := smap (fun f x => TmPack id arg ty (f x)) (
        let recursed := grand_unified_subst curry in
        match arg with
        | None => recursed
        | Some a => remove_key_if_head a recursed
        end) in
      let hi := smap (fun f x => TmPack id arg (f x) curry) (structural_grand_unified_subst ty) in
      partition_pf fst_cmp hi lo ++ lo
  | TmForA arg ty body =>
      let lo := smap (fun f x => TmForA arg ty (f x)) (
        let recursed := grand_unified_subst body in
        match arg with
        | None => recursed
        | Some a => remove_key_if_head a recursed
        end) in
      let hi := smap (fun f x => TmForA arg (f x) body) (structural_grand_unified_subst ty) in
      partition_pf fst_cmp hi lo ++ lo
  | TmAppl a b =>
      smap (fun f x => TmAppl (f x) b) (grand_unified_subst a) ++
      smap (fun f x => TmAppl a (f x)) (grand_unified_subst b)
  end.

Definition subst x y t := option_map (fun f => f y) (pair_lookup x (grand_unified_subst t)).
Arguments subst x y t/.

Example subst_simple : forall f x,
  subst f TmVoid (TmAppl (TmVarS f) x) = Some (TmAppl TmVoid x).
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example grand_unified_subst_simple :
  grand_unified_subst (TmAppl (TmVarS "f"%string) (TmVarS "x"%string)) = [
    ("f"%string, fun t => TmAppl t (TmVarS "x"%string));
    ("x"%string, fun t => TmAppl (TmVarS "f"%string) t)].
Proof. reflexivity. Qed.

Example grand_unified_subst_lambda :
  grand_unified_subst (TmForA (Some "x") (TmVarS "T") (TmAppl (TmVarS "x") (TmVarS "x")))%string = [
    ("T", fun x => TmForA (Some "x") x (TmAppl (TmVarS "x") (TmVarS "x")));
    (* ignore the first `x`, since it's bound, then *)
    ("x", fun x => TmForA (Some "x") (TmVarS "T") (TmAppl (TmVarS "x") x))]%string.
Proof. reflexivity. Qed.

Lemma fst_cmp_eqb : forall {T} a a' b b',
  @fst_cmp T T (a, b) (a', b') = eqb a a'.
Proof. reflexivity. Qed.

Theorem grand_unified_subst_fv : forall t,
  fv t = map fst (grand_unified_subst t).
Proof.
  induction t; intros; simpl in *; try reflexivity; repeat rewrite slow_down; repeat rewrite <- partition_pf_fast_slow;
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
  let P := fun p : _ * _ => let (x, f) := p in f (TmVarS x) = t in
  Forall P (grand_unified_subst t).
Proof.
  induction t as [| | | | id arg a IHa b IHb | arg a IHa b IHb | a IHa b IHb]; simpl in *; repeat constructor; [| |
    apply Forall_app; split; apply Forall_smap; (eapply Forall_impl; [| try apply IHa; apply IHb]);
    intros; destruct a0; rewrite H; reflexivity]; repeat rewrite slow_down; destruct arg;
  apply Forall_app; (split; [eapply incl_Forall; [apply incl_partition_pf_fst |] |]);
  apply Forall_smap; try (eapply incl_Forall; [apply remove_key_if_head_incl |]);
  (eapply Forall_impl; [| try apply structural_grand_unified_subst_id; apply IHb]);
  intros; destruct a0; rewrite H; reflexivity.
Qed.

Theorem subst_id : forall x t s,
  subst x (TmVarS x) t = Some s ->
  s = t.
Proof.
  intros. unfold subst in *. destruct (pair_lookup x (grand_unified_subst t)) eqn:Ep; invert H.
  eapply pair_lookup_Forall in Ep; [| apply grand_unified_subst_id]. assumption.
Qed.
