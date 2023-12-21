From Coq Require Import
  Lists.List.
Import ListNotations.
From Lang Require Import
  FreeVariables
  Invert
  Mint
  Terms.

Fixpoint smap
  (f : (term -> term) -> term -> term)
  (x : list (string * (term -> term))) :
  list (string * (term -> term)) :=
  match x with
  | [] => []
  | (s, g) :: tl => (s, f g) :: smap f tl
  end.

Theorem smap_distr : forall f a b,
  smap f (a ++ b) = smap f a ++ smap f b.
Proof.
  intros f a. generalize dependent f. induction a; intros; simpl in *.
  { reflexivity. } destruct a. rewrite IHa. reflexivity.
Qed.

Theorem smap_len : forall f li,
  Datatypes.length (smap f li) = Datatypes.length li.
Proof.
  intros f li. generalize dependent f. induction li; intros; simpl in *.
  { reflexivity. } destruct a. simpl. rewrite IHli. reflexivity.
Qed.

Theorem map_fst_smap : forall f li,
  map fst (smap f li) = map fst li.
Proof. induction li. { reflexivity. } destruct a. simpl. rewrite IHli. reflexivity. Qed.

Fixpoint remove_key_all {T} x (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, f) :: tl =>
      let recursed := remove_key_all x tl in
      if eqb x s then recursed else (s, f) :: recursed
  end.

Definition remove_key_if_head {T} x (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, f) :: tl => if eqb x s then tl else li
  end.

Lemma remove_all_key_eq : forall {T} x (li : list (string * T)),
  map fst (remove_key_all x li) = remove_all x (map fst li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. destruct (eqb x s) eqn:E. { apply IHli. } simpl. f_equal. apply IHli.
Qed.

Lemma remove_if_head_key_eq : forall {T} x (li : list (string * T)),
  map fst (remove_key_if_head x li) = remove_if_head x (map fst li).
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. destruct (eqb x s) eqn:E. { reflexivity. } simpl. reflexivity.
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
      smap (fun f x => TmPack id arg (f x) curry) (grand_unified_subst ty) ++
      smap (fun f x => TmPack id arg ty (f x)) (
        let recursed := grand_unified_subst curry in
        match arg with
        | None => recursed
        | Some a =>
            (if mint ty then remove_key_all else remove_key_if_head) a recursed
        end)
  | TmForA arg ty body =>
      smap (fun f x => TmForA arg (f x) body) (grand_unified_subst ty) ++
      smap (fun f x => TmForA arg ty (f x)) (
        let recursed := grand_unified_subst body in
        match arg with
        | None => recursed
        | Some a =>
            (if mint ty then remove_key_all else remove_key_if_head) a recursed
        end)
  | TmAppl a b =>
      smap (fun f x => TmAppl (f x) b) (grand_unified_subst a) ++
      smap (fun f x => TmAppl a (f x)) (grand_unified_subst b)
  end.

Fixpoint pair_lookup {V} key (pairs : list (string * V)) :=
  match pairs with
  | [] => None
  | (k, v) :: tl => if eqb key k then Some v else pair_lookup key tl
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

Theorem grand_unified_subst_exactly_fv : forall t,
  fv t = map fst (grand_unified_subst t).
Proof.
  intros t. induction t; intros; subst; simpl in *; try reflexivity;
  repeat rewrite IHt1; repeat rewrite IHt2; try destruct arg; destruct (reflect_mint t1);
  repeat rewrite map_distr; repeat rewrite map_fst_smap; f_equal;
  try (symmetry; apply remove_all_key_eq); destruct (grand_unified_subst t2); try reflexivity;
  destruct p; simpl; destruct (eqb s s0); reflexivity.
Qed.
(* WOOHOOOOOOOOOOOOOOO *)

Lemma pair_lookup_smap : forall f x li,
  pair_lookup x (smap f li) = option_map f (pair_lookup x li).
Proof.
  intros f x li. generalize dependent x. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. destruct (eqb x s) eqn:E. { reflexivity. } apply IHli.
Qed.

Lemma pair_lookup_app : forall {T} x a b,
  @pair_lookup T x (a ++ b) =
  match pair_lookup x a with
  | None => pair_lookup x b
  | Some out => Some out
  end.
Proof.
  intros T x a. generalize dependent x. induction a; intros; simpl in *. { reflexivity. }
  destruct a. destruct (eqb x s). { reflexivity. } apply IHa.
Qed.

Lemma pair_lookup_Forall_snd : forall {T} P li x y,
  Forall P (map snd li) ->
  @pair_lookup T x li = Some y ->
  P y.
Proof.
  intros T P li x y Hf Hl. generalize dependent y. generalize dependent x.
  remember (map snd li) eqn:Emap. generalize dependent li.
  induction Hf; intros; destruct li; invert Emap; try discriminate Hl.
  destruct p. simpl in *. destruct (eqb x0 s) eqn:E. { invert Hl. assumption. }
  eapply IHHf; [reflexivity |]. apply Hl.
Qed.

Lemma pair_lookup_Forall : forall {T} P li x t,
  Forall P li ->
  @pair_lookup T x li = Some t ->
  P (x, t).
Proof.
  intros T P li x t Hf Hl. generalize dependent t. generalize dependent x.
  induction Hf; intros; simpl in *. { discriminate Hl. } destruct x as [k v].
  destruct (eqb x0 k) eqn:E; [apply eqb_eq in E; invert Hl | apply IHHf]; assumption.
Qed.

Theorem Forall_smap : forall f P li,
  Forall (fun p : _ * _ => let (x, g) := p in P (x, f g)) li ->
  Forall P (smap f li).
Proof.
  intros. remember (fun p : string * (term -> term) => let (x, g) := p in P (x, f g)) as F eqn:EF.
  generalize dependent P. generalize dependent f. induction H; intros; [apply Forall_nil |].
  destruct x as [s g]. subst. simpl in *. constructor; [assumption |]. apply IHForall. reflexivity.
Qed.

Lemma remove_key_all_incl : forall {T} x (li : list (string * T)),
  incl (remove_key_all x li) li.
Proof.
  unfold incl. intros T x li. generalize dependent x. induction li; intros; simpl in *. { destruct H. }
  destruct a. destruct (eqb x s) eqn:E. { apply eqb_eq in E. subst. right. eapply IHli. apply H. }
  destruct a0. destruct H. { left. assumption. } right. eapply IHli. apply H.
Qed.

Lemma remove_key_if_head_incl : forall {T} x (li : list (string * T)),
  incl (remove_key_if_head x li) li.
Proof.
  unfold incl. intros T x [] [a1 a2] H. { inversion H. } destruct p. simpl in H. destruct (eqb x s); [right |]; assumption.
Qed.

Theorem grand_unified_subst_id : forall t,
  let P := fun p : _ * _ => let (x, f) := p in f (TmVarS x) = t in
  Forall P (grand_unified_subst t).
Proof.
  induction t as [| | | | id arg a IHa b IHb | arg a IHa b IHb | a IHa b IHb];
  subst; simpl in *; try solve [repeat constructor];
  apply Forall_app; split; apply Forall_smap; try destruct arg;
  try (eapply Forall_impl; [| try apply IHa; try apply IHb; apply H2]; intros; destruct a0; f_equal; assumption);
  destruct (reflect_mint a); eapply incl_Forall; try apply remove_key_all_incl; try apply remove_key_if_head_incl;
  try (eapply Forall_impl; [| try apply IHa; try apply IHb; apply H2]; intros; destruct a0; f_equal; assumption).
Qed.

Theorem subst_id : forall x t s,
  subst x (TmVarS x) t = Some s ->
  s = t.
Proof.
  intros. unfold subst in *. destruct (pair_lookup x (grand_unified_subst t)) eqn:Ep; invert H.
  eapply pair_lookup_Forall in Ep; [| apply grand_unified_subst_id]. assumption.
Qed.
