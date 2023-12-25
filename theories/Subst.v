From Coq Require Import
  Lists.List.
Import ListNotations.
From Lang Require Import
  DupFrom
  FreeVariables
  Invert
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

Lemma remove_key_all_eq : forall {T} x li,
  ~In x (map fst li) ->
  @remove_key_all T x li = li.
Proof.
  intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl in *. apply Decidable.not_or in H as [H1 H2]. apply eqb_neq in H1.
  rewrite eqb_sym in H1. rewrite H1. f_equal. apply IHli. assumption.
Qed.

Definition fst_cmp {A B} := fun (a : string * A) (b : string * B) => eqb (fst a) (fst b).

(* Ludicrous that this is the easiest correct definition to write.
 * Generates substitution functions for every free variable at once. *)
Fixpoint grand_unified_subst_with rm t : list (string * (term -> term)) :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      []
  | TmVarS s =>
      [(s, fun x => x)]
  | TmPack id arg ty curry =>
      dup_from_src_with fst_cmp
      (smap (fun f x => TmPack id arg (f x) curry) (grand_unified_subst_with remove_key_all ty))
      (smap (fun f x => TmPack id arg ty (f x)) (
        let recursed := grand_unified_subst_with rm curry in
        match arg with
        | None => recursed
        | Some a => rm a recursed
        end))
  | TmForA arg ty body =>
      dup_from_src_with fst_cmp
      (smap (fun f x => TmForA arg (f x) body) (grand_unified_subst_with remove_key_all ty))
      (smap (fun f x => TmForA arg ty (f x)) (
        let recursed := grand_unified_subst_with rm body in
        match arg with
        | None => recursed
        | Some a => rm a recursed
        end))
  | TmAppl a b =>
      smap (fun f x => TmAppl (f x) b) (grand_unified_subst_with rm a) ++
      smap (fun f x => TmAppl a (f x)) (grand_unified_subst_with rm b)
  end.
Definition grand_unified_subst := grand_unified_subst_with remove_key_if_head.
Arguments grand_unified_subst/ t.

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

Lemma has_cmp_fst : forall {T} li s t,
  has_with (@fst_cmp T T) (s, t) li = has_with eqb s (map fst li).
Proof.
  intros T li. induction li; intros; simpl in *. { reflexivity. }
  destruct a. unfold fst_cmp. simpl in *. destruct (eqb s s0). { reflexivity. }
  apply IHli.
Qed.

Lemma has_fst_or : forall {T} x a b,
  @has_with (string * T) (string * T) fst_cmp x (dup_from_src_with fst_cmp a b) =
  orb (has_with fst_cmp x a) (has_with fst_cmp x b).
Proof.
  intros T x a. generalize dependent x. induction a; intros; simpl in *. { reflexivity. }
  destruct (has_with fst_cmp a (dup_from_src_with fst_cmp a0 b)) eqn:Eh; simpl in *;
  (destruct (fst_cmp x a) eqn:Ef; simpl in *; [| apply IHa]). 2: reflexivity.
  destruct a. destruct x. rewrite has_cmp_fst in *.
  unfold fst_cmp in Ef. simpl in *. apply eqb_eq in Ef. subst. assumption.
Qed.

Lemma dup_from_src_fst : forall {T} a b,
  map fst (dup_from_src_with fst_cmp a b) = dup_from_src_with eqb (map (@fst _ T) a) (map fst b).
Proof.
  intros T a. induction a; intros; simpl in *. { reflexivity. }
  destruct a. simpl in *. rewrite has_cmp_fst. rewrite IHa.
  destruct (has_with eqb s (dup_from_src_with eqb (map fst a0) (map fst b)));
  [| simpl in *; f_equal]; apply IHa.
Qed.

Lemma dup_from_src_nil_exists : forall {T} a b, exists pre,
  dup_from_src_with (@fst_cmp _ T) a b = pre ++ b.
Proof.
  induction a; intros; simpl in *. { exists []. reflexivity. }
  destruct (has_with fst_cmp a (dup_from_src_with fst_cmp a0 b)). { apply IHa. }
  destruct (IHa b) as [x H]. exists (a :: x). simpl. f_equal. assumption.
Qed.

Fixpoint set_diff {T} (a b : list (string * T)) :=
  match a with
  | [] => []
  | hd :: tl =>
      let recursed := set_diff tl b in
      if has_with fst_cmp hd b then recursed else hd :: recursed
  end.

Lemma dup_from_src_nil : forall {T} a b,
  dup_from_src_with (@fst_cmp _ T) a b = set_diff a b ++ b.
Proof.
  induction a; intros; simpl in *. { reflexivity. }
  destruct (has_with fst_cmp a (dup_from_src_with fst_cmp a0 b)) eqn:Eh;
  rewrite has_fst_or in Eh; rewrite IHa; [| rewrite app_comm_cons]; f_equal.
  - apply Bool.orb_prop in Eh. destruct Eh; [| rewrite H; reflexivity].
    + admit.
    + rewrite H.

  destruct (has_with fst_cmp a b) eqn:Eh; rewrite has_fst_or; rewrite Eh. { rewrite Bool.orb_true_r. apply IHa. }
  destruct (has_with fst_cmp a a0) eqn:E0; simpl in *; rewrite IHa; rewrite app_comm_cons; f_equal.
Qed.

Theorem grand_unified_subst_structural_fv : forall t,
  fv_with remove_all t = map fst (grand_unified_subst_with remove_key_all t).
Proof.
  induction t; intros; subst; simpl in *; try reflexivity;
  repeat rewrite IHt1; repeat rewrite IHt2; [| | repeat rewrite map_distr; repeat rewrite map_fst_smap; reflexivity];
  destruct arg; repeat rewrite <- remove_all_key_eq; rewrite dup_from_src_fst; repeat rewrite map_fst_smap; reflexivity.
Qed.

Theorem grand_unified_subst_fv : forall t,
  fv t = map fst (grand_unified_subst t).
Proof.
  induction t; intros; subst; simpl in *; try reflexivity;
  repeat rewrite IHt1; repeat rewrite IHt2; [| | rewrite map_distr; repeat rewrite map_fst_smap; reflexivity];
  rewrite dup_from_src_fst; repeat rewrite map_fst_smap; rewrite grand_unified_subst_structural_fv;
  (destruct arg; [| reflexivity]); (destruct (grand_unified_subst_with remove_key_if_head t2) eqn:Eg; [reflexivity |]);
  destruct p; simpl in *; (destruct (eqb s s0); reflexivity).
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

(* God this is the dumbest function of all time but it's only ever used in proofs *)
Fixpoint slow_unique_key {T} (li : list (string * T)) :=
  match li with
  | [] => []
  | (s, t) :: tl => (s, t) :: remove_key_all s (slow_unique_key tl)
  end.

Lemma has_remove_key_all : forall {T} (x y : string * T) (li : list (string * T)),
  fst_cmp x y = false ->
  has_with fst_cmp x (remove_key_all (fst y) li) = has_with fst_cmp x li.
Proof.
  intros. generalize dependent y. generalize dependent x. induction li; intros; simpl in *. { reflexivity. }
  destruct a. destruct x. destruct y. unfold fst_cmp in *. simpl in *.
  destruct (eqb s1 s) eqn:E1. { apply eqb_eq in E1. subst. rewrite H. apply (IHli (s0, t0) (s, t)). assumption. }
  destruct (eqb s0 s) eqn:E0; simpl in *. { rewrite E0. reflexivity. } rewrite E0. apply (IHli (s0, t0) (s1, t1)). assumption.
Qed.

Lemma has_slow_unique : forall {T} x li,
  has_with (@fst_cmp T T) x (slow_unique_key li) = has_with fst_cmp x li.
Proof.
  intros T [s t] li. generalize dependent t. generalize dependent s.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. destruct (eqb_spec s s0). { subst. unfold fst_cmp. simpl. rewrite eqb_refl. reflexivity. }
  simpl. rewrite (has_remove_key_all (s, t) (s0, t0)). 2: { unfold fst_cmp. simpl. apply eqb_neq. assumption. }
  unfold fst_cmp. simpl. apply eqb_neq in n. rewrite n. apply IHli.
Qed.

Lemma dup_from_src_fst_nil : forall {T} (a : list (string * T)),
  dup_from_src_with fst_cmp a [] = slow_unique_key a.
Proof.
  induction a; intros; simpl in *. { reflexivity. }
  destruct a. rewrite IHa. destruct (has_with fst_cmp (s, t) (slow_unique_key a0)) eqn:Eh. Abort.

Lemma dup_with_src_fst_app_exists : forall {T} a b, exists pre,
  @dup_from_src_with (string * T) fst_cmp a b = pre ++ b.
Proof.
  induction a; intros; simpl in *. { exists []. reflexivity. }
  destruct (IHa b) as [x H]. rewrite H. destruct (has_with fst_cmp a (x ++ b));
  [exists x | exists (a :: x); simpl; f_equal]; reflexivity.
Qed.

Lemma has_fst_or : forall {T} x a b,
  @has_with (string * T) (string * T) fst_cmp x (dup_from_src_with fst_cmp a b) =
  orb (has_with fst_cmp x a) (has_with fst_cmp x b).
Proof.
  intros T x a. generalize dependent x. induction a; intros; simpl in *. { reflexivity. }
  destruct (has_with fst_cmp a (dup_from_src_with fst_cmp a0 b)) eqn:Eh; simpl in *;
  (destruct (fst_cmp x a) eqn:Ef; simpl in *; [| apply IHa]). 2: reflexivity.
  destruct a. destruct x. rewrite has_cmp_fst in *.
  unfold fst_cmp in Ef. simpl in *. apply eqb_eq in Ef. subst. assumption.
Qed.

Lemma dup_with_src_fst_app : forall {T} a b,
  @dup_from_src_with (string * T) fst_cmp a b =
  fold_left (fun acc x => remove_key_all (fst x) acc) b (slow_unique_key a) ++ b.
Proof.
  induction a; intros; simpl in *. {
    rewrite <- (app_nil_l b). f_equal. simpl. induction b; simpl. { reflexivity. } apply IHb. }
  destruct a. destruct (has_with fst_cmp (s, t) (dup_from_src_with fst_cmp a0 b)) eqn:Eh;
  rewrite IHa; [| rewrite app_comm_cons]; f_equal.
  - remember (dup_from_src_with fst_cmp a0 b) as d eqn:Ed. generalize dependent s. generalize dependent t.
    generalize dependent a0. generalize dependent b. induction d; intros; simpl in *. { discriminate Eh. }
    rewrite has_cmp_fst in Eh. apply has_in_iff in Eh; [| apply eqb_eq]. destruct Eh.
    2: { apply IHl. rewrite has_cmp_fst. apply has_in_iff. { apply eqb_eq. } assumption. }
    apply IHl.

  - rewrite has_fst_or in Eh. apply Bool.orb_false_iff in Eh as [H1 H2]. rewrite has_cmp_fst in *.
    induction b; simpl in *. f_equal. rewrite remove_key_all_eq.
    + reflexivity.
    + intro C. eapply has_in_iff in C; [| apply eqb_eq]. erewrite <- has_cmp_fst in C. Search (has_with eqb). { rewrite H1 in C. } Search remove_key_all.

    + rewrite has_fst_or. rewrite Eh. simpl in *. rewrite IHa. f_equal. 
    specialize (IHa b).
    apply IHa.
  destruct (IHa b) as [x H]. rewrite H. destruct (has_with fst_cmp a (x ++ b));
  [exists x | exists (a :: x); simpl; f_equal]; reflexivity.
Qed.

Theorem grand_unified_subst_structural_id : forall t,
  let P := fun p : _ * _ => let (x, f) := p in f (TmVarS x) = t in
  Forall P (grand_unified_subst_with remove_key_all t).
Proof.
  induction t as [| | | | id arg a IHa b IHb | arg a IHa b IHb | a IHa b IHb];
  subst; simpl in *; try solve [repeat constructor]; [| |
    apply Forall_app; split; apply Forall_smap; (eapply Forall_impl; [| try apply IHa; apply IHb]);
    intros; destruct a0; rewrite H; reflexivity];
  simpl. Search dup_from_src_with.
  remember (grand_unified_subst_with remove_key_all a) as g eqn:Eg; [generalize dependent id |];
  generalize dependent arg; generalize dependent a; generalize dependent b; (
    induction g; intros; simpl in *; [
      apply Forall_smap; destruct arg; [eapply incl_Forall; [apply remove_key_all_incl |] |];
      (eapply Forall_impl; [| apply IHb]); intros; destruct a0; rewrite H; reflexivity |]);
  destruct a; simpl in *; rewrite has_cmp_fst; rewrite dup_from_src_fst; repeat rewrite map_fst_smap;
  destruct arg.
  - admit.
  - specialize (IHg _ IHb). clear IHg IHb IHa Eg. simpl in *. Search (map fst). rewrite has_cmp_fst. Search (has_with fst_cmp).

Theorem grand_unified_subst_id : forall t,
  let P := fun p : _ * _ => let (x, f) := p in f (TmVarS x) = t in
  Forall P (grand_unified_subst t).
Proof.
  induction t as [| | | | id arg a IHa b IHb | arg a IHa b IHb | a IHa b IHb];
  subst; simpl in *; try solve [repeat constructor]; [| |
    apply Forall_app; split; apply Forall_smap; (eapply Forall_impl; [| try apply IHa; apply IHb]);
    intros; destruct a0; rewrite H; reflexivity];
  repeat rewrite dup_from_src_fst. simpl in *.

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
