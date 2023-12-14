From Coq Require Import
  Lists.List.
Import ListNotations.
From Adam Require Import
  Invert
  Terms.

Variant resource T := Unused | Used (output : T).
Arguments Unused {T}.
Arguments Used {T} output.

Definition rmap : forall {A B}, (A -> B) -> resource A -> resource B := fun _ _ f r =>
  match r with
  | Unused => Unused
  | Used x => Used (f x)
  end.

Fixpoint count_free_slow x t :=
  match t with
  | TmVarS s =>
      if eqb x s then 1 else 0
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      count_free_slow x a + count_free_slow x b
  | TmPack _ (Some arg) a b
  | TmForA (Some arg) a b =>
      if eqb x arg then 0 else
      count_free_slow x a + count_free_slow x b
  | _ => 0
  end.
Fixpoint count_free_fast acc x t :=
  match t with
  | TmVarS s =>
      if eqb x s then S acc else acc
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      count_free_fast (count_free_fast acc x a) x b
  | TmPack _ (Some arg) a b
  | TmForA (Some arg) a b =>
      if eqb x arg then acc else
      count_free_fast (count_free_fast acc x a) x b
  | _ => acc
  end.
Lemma count_free_fast_acc_sum : forall x acc t,
  count_free_fast acc x t = acc + count_free_fast 0 x t.
Proof.
  intros. generalize dependent x. generalize dependent acc.
  induction t; intros; simpl in *; try rewrite Nat.add_0_r; try reflexivity.
  - destruct (eqb x id) eqn:E; try rewrite Nat.add_0_r; try rewrite Nat.add_1_r; reflexivity.
  - destruct arg.
    + destruct (eqb x s) eqn:E. { rewrite Nat.add_0_r. reflexivity. }
      rewrite IHt1. rewrite IHt2. rewrite <- Nat.add_assoc. f_equal. symmetry. apply IHt2.
    + rewrite IHt2. rewrite IHt1. rewrite <- Nat.add_assoc. f_equal. symmetry. apply IHt2.
  - destruct arg.
    + destruct (eqb x s) eqn:E. { rewrite Nat.add_0_r. reflexivity. }
      rewrite IHt1. rewrite IHt2. rewrite <- Nat.add_assoc. f_equal. symmetry. apply IHt2.
    + rewrite IHt2. rewrite IHt1. rewrite <- Nat.add_assoc. f_equal. symmetry. apply IHt2.
  - rewrite IHt2. rewrite IHt1. rewrite <- Nat.add_assoc. f_equal. symmetry. apply IHt2.
Qed.
Theorem count_free_eq : forall x t,
  count_free_slow x t = count_free_fast 0 x t.
Proof.
  intros. generalize dependent x. induction t; intros; try reflexivity; simpl in *;
  try (destruct arg; [destruct (eqb x s); [reflexivity |] |]);
  rewrite count_free_fast_acc_sum; rewrite IHt1; rewrite IHt2; reflexivity.
Qed.

Inductive CountFree x : term -> nat -> Prop :=
  | CountFreeVoid :
      CountFree x TmVoid 0
  | CountFreeStar : forall lvl,
      CountFree x (TmStar lvl) 0
  | CountFreeVarE :
      CountFree x (TmVarS x) 1
  | CountFreeVarD : forall s,
      x <> s ->
      CountFree x (TmVarS s) 0
  | CountFreeAtom : forall id lvl,
      CountFree x (TmAtom id lvl) 0
  | CountFreePackNone : forall id ty curry a b c,
      CountFree x ty a ->
      CountFree x curry b ->
      a + b = c ->
      CountFree x (TmPack id None ty curry) c
  | CountFreePackSomeE : forall id ty curry,
      CountFree x (TmPack id (Some x) ty curry) 0
  | CountFreePackSomeD : forall id s ty curry a b c,
      x <> s ->
      CountFree x ty a ->
      CountFree x curry b ->
      a + b = c ->
      CountFree x (TmPack id (Some s) ty curry) c
  | CountFreeForANone : forall ty body a b c,
      CountFree x ty a ->
      CountFree x body b ->
      a + b = c ->
      CountFree x (TmForA None ty body) c
  | CountFreeForASomeE : forall ty body,
      CountFree x (TmForA (Some x) ty body) 0
  | CountFreeForASomeD : forall s ty body a b c,
      x <> s ->
      CountFree x ty a ->
      CountFree x body b ->
      a + b = c ->
      CountFree x (TmForA (Some s) ty body) c
  | CountFreeAppl : forall f y a b c,
      CountFree x f a ->
      CountFree x y b ->
      a + b = c ->
      CountFree x (TmAppl f y) c
  .
Theorem reflect_count_free_slow : forall x t n,
  count_free_slow x t = n <-> CountFree x t n.
Proof.
  split; intros.
  - generalize dependent x. generalize dependent n. induction t; intros; simpl in *; subst; try solve [constructor];
    try (destruct arg; [destruct (eqb x s) eqn:E; [rewrite eqb_eq in E; subst; constructor |] |]);
    try econstructor; try eapply IHt1; try eapply IHt2; try reflexivity;
    try destruct (eqb x id) eqn:E; try rewrite eqb_eq in E; subst; try constructor; apply eqb_neq; assumption.
  - induction H; simpl in *; repeat rewrite eqb_refl; try (apply eqb_neq in H; rewrite H);
    try rewrite IHCountFree1; try rewrite IHCountFree2; try assumption; try reflexivity.
Qed.
Theorem reflect_count_free_fast : forall x t n,
  count_free_fast 0 x t = n <-> CountFree x t n.
Proof. intros. rewrite <- count_free_eq. apply reflect_count_free_slow. Qed.
Definition count_free := count_free_fast 0.
Arguments count_free/ x t.
Theorem reflect_count_free : forall x t n,
  count_free x t = n <-> CountFree x t n.
Proof. intros. apply reflect_count_free_fast. Qed.

(* Resource-aware substitution: substitute exactly once. *)
Fixpoint subst pre post t :=
  match t with
  | TmVoid | TmStar _ | TmAtom _ _ => Unused
  | TmVarS id => if eqb pre id then Used post else Unused
  | TmPack id None ty curry =>
      match subst pre post ty with
      | Unused => rmap (TmPack id None ty) (subst pre post curry)
      | Used ty' => Used (TmPack id None ty' curry)
      end
  | TmPack id (Some arg) ty curry => if eqb pre arg then Unused else
      match subst pre post ty with
      | Unused => rmap (TmPack id (Some arg) ty) (subst pre post curry)
      | Used ty' => Used (TmPack id (Some arg) ty' curry)
      end
  | TmForA None ty body =>
      match subst pre post ty with
      | Unused => rmap (TmForA None ty) (subst pre post body)
      | Used ty' => Used (TmForA None ty' body)
      end
  | TmForA (Some arg) ty body => if eqb pre arg then Unused else
      match subst pre post ty with
      | Unused => rmap (TmForA (Some arg) ty) (subst pre post body)
      | Used ty' => Used (TmForA (Some arg) ty' body)
      end
  | TmAppl f x =>
      match subst pre post f with
      | Unused => rmap (TmAppl f) (subst pre post x)
      | Used f' => Used (TmAppl f' x)
      end
  end.
Inductive Subst (pre : string) (post : term) : term -> term -> Prop :=
  | SubstVarE :
      Subst pre post (TmVarS pre) post
  | SubstPackNoneL : forall id ty ty' curry,
      Subst pre post ty ty' ->
      Subst pre post (TmPack id None ty curry) (TmPack id None ty' curry)
  | SubstPackNoneR : forall id ty curry curry',
      CountFree pre ty 0 ->
      Subst pre post curry curry' ->
      Subst pre post (TmPack id None ty curry) (TmPack id None ty curry')
  | SubstPackSomeL : forall id arg ty ty' curry,
      pre <> arg ->
      Subst pre post ty ty' ->
      Subst pre post (TmPack id (Some arg) ty curry) (TmPack id (Some arg) ty' curry)
  | SubstPackSomeR : forall id arg ty curry curry',
      pre <> arg ->
      CountFree pre ty 0 ->
      Subst pre post curry curry' ->
      Subst pre post (TmPack id (Some arg) ty curry) (TmPack id (Some arg) ty curry')
  | SubstForANoneL : forall ty ty' body,
      Subst pre post ty ty' ->
      Subst pre post (TmForA None ty body) (TmForA None ty' body)
  | SubstForANoneR : forall ty body body',
      CountFree pre ty 0 ->
      Subst pre post body body' ->
      Subst pre post (TmForA None ty body) (TmForA None ty body')
  | SubstForASomeL : forall arg ty ty' body,
      pre <> arg ->
      Subst pre post ty ty' ->
      Subst pre post (TmForA (Some arg) ty body) (TmForA (Some arg) ty' body)
  | SubstForASomeR : forall arg ty body body',
      pre <> arg ->
      CountFree pre ty 0 ->
      Subst pre post body body' ->
      Subst pre post (TmForA (Some arg) ty body) (TmForA (Some arg) ty body')
  | SubstApplL : forall f f' x,
      Subst pre post f f' ->
      Subst pre post (TmAppl f x) (TmAppl f' x)
  | SubstApplR : forall f x x',
      CountFree pre f 0 ->
      Subst pre post x x' ->
      Subst pre post (TmAppl f x) (TmAppl f x')
  .
(*
Lemma subst_available_iff_never_used : forall pre post t,
  Subst pre post t Unused <-> forall t', ~Subst pre post t (Used t').
Proof.
  split; intros.
  - intro C. generalize dependent t'. remember Unused as r eqn:E.
    induction H; intros; simpl in *; invert E; invert C; try contradiction;
    try solve [apply (IHSubst1 eq_refl ty'); assumption];
    try solve [apply (IHSubst2 eq_refl curry'); assumption];
    try solve [apply (IHSubst2 eq_refl body'); assumption];
    try solve [apply (IHSubst1 eq_refl f'); assumption];
    try solve [apply (IHSubst2 eq_refl x'); assumption].
  - generalize dependent pre. generalize dependent post.
    induction t; intros; simpl in *; try constructor.
    + intros C. subst. contradiction (H post). constructor.
    + destruct arg.
      * destruct (eqb pre s) eqn:E. { rewrite eqb_eq in E. subst. constructor. }
        rewrite eqb_neq in E. constructor; [assumption | apply IHt1 | apply IHt2];
        intros t' C; eapply H. { apply SubstPackSomeL; [assumption | apply C]. }
        apply SubstPackSomeR; [assumption | | apply C].
        apply IHt1. intros t'' C'. eapply H. apply SubstPackSomeL. { assumption. } apply C'.
      * constructor; [apply IHt1 | apply IHt2]; intros t' C; eapply H. { apply SubstPackNoneL. apply C. }
        apply SubstPackNoneR; [| apply C]. apply IHt1. intros t'' C'. eapply H. apply SubstPackNoneL. apply C'.
    + destruct arg.
      * destruct (eqb pre s) eqn:E. { rewrite eqb_eq in E. subst. constructor. }
        rewrite eqb_neq in E. constructor; [assumption | apply IHt1 | apply IHt2];
        intros t' C; eapply H. { apply SubstForASomeL; [assumption | apply C]. }
        apply SubstForASomeR; [assumption | | apply C].
        apply IHt1. intros t'' C'. eapply H. apply SubstForASomeL. { assumption. } apply C'.
      * constructor; [apply IHt1 | apply IHt2]; intros t' C; eapply H. { apply SubstForANoneL. apply C. }
        apply SubstForANoneR; [| apply C]. apply IHt1. intros t'' C'. eapply H. apply SubstForANoneL. apply C'.
    + apply IHt1. intros t' C. eapply H. constructor. apply C.
    + apply IHt2. intros t' C. eapply H. apply SubstApplR; [| apply C].
      apply IHt1. intros t'' C'. eapply H. constructor. apply C'.
Qed.
*)

Theorem subst_iff_count_nonzero_prop : forall pre post t,
  count_free pre t = 0 <-> forall t', ~Subst pre post t t'.
Proof.
  split; intros.
  - intro C. induction C; simpl in *; [rewrite eqb_refl in H; discriminate H | | | | | | | | | |];
    rewrite count_free_fast_acc_sum in *;
    try destruct (count_free_fast 0 pre f);
    try destruct (count_free_fast 0 pre x);
    try destruct (count_free_fast 0 pre ty);
    try destruct (count_free_fast 0 pre body);
    try destruct (count_free_fast 0 pre curry);
    try (apply eqb_neq in H0; rewrite H0 in * );
    try discriminate H; try apply (IHC eq_refl).
  - generalize dependent pre. generalize dependent post. induction t; intros; simpl in *; try reflexivity;
    try rewrite count_free_fast_acc_sum; try destruct arg;
    try destruct (eqb pre s) eqn:Es; try apply eqb_neq in Es;
    try erewrite IHt1; try erewrite IHt2; try reflexivity; try intros t' C; try eapply H;
    try solve [constructor; try assumption; apply C];
    try (apply SubstPackSomeR; [assumption | | apply C]);
    try (apply SubstPackNoneR; [| apply C]);
    try (apply SubstForASomeR; [assumption | | apply C]);
    try (apply SubstForANoneR; [| apply C]);
    try (apply SubstApplR; [| apply C]);
    try apply reflect_count_free; try eapply IHt1; try eapply IHt2; try intros t'' C'; try eapply H;
    try (constructor; try assumption; apply C').
    destruct (eqb pre id) eqn:E; [| reflexivity]. apply eqb_eq in E. subst. contradiction (H post). constructor.
Qed.

Theorem reflect_not_subst : forall pre post t,
  subst pre post t = Unused <-> forall t', ~Subst pre post t t'.
Proof.
  split; intros.
  - intro C. generalize dependent H. induction C; intros; simpl in *;
    try rewrite eqb_refl in *; try apply eqb_neq in H; try rewrite H in *;
    try destruct (subst pre post ty); try destruct (subst pre post curry);
    try destruct (subst pre post body); try destruct (subst pre post f); try destruct (subst pre post x);
    try apply (IHC eq_refl); try discriminate.
  - generalize dependent pre. generalize dependent post. induction t; intros; simpl in *; try reflexivity;
    [destruct (eqb pre id) eqn:Ei; [| reflexivity]; apply eqb_eq in Ei; subst;
      contradiction (H post); constructor | | |];
    try (destruct arg; [destruct (eqb pre s) eqn:Es; [reflexivity |]; apply eqb_neq in Es |]);
    (destruct (subst pre post t1) eqn:E1; [|
      rewrite IHt1 in E1; [discriminate E1 |]; intros t' C; eapply H; constructor; try assumption; apply C]);
    destruct (subst pre post t2) eqn:E2; try reflexivity; simpl in *;
    (rewrite IHt2 in E2; [discriminate E2 |]); intros t' C; eapply H;
    try apply SubstPackSomeR; try apply SubstPackNoneR;
    try apply SubstForASomeR; try apply SubstForANoneR;
    try apply SubstApplR; try assumption; try apply C;
    apply reflect_count_free; apply subst_iff_count_nonzero_prop in H;
    simpl in *; try (apply eqb_neq in Es; rewrite Es in H);
    rewrite count_free_fast_acc_sum in H; (destruct (count_free_fast 0 pre t1); [reflexivity | discriminate H]).
Qed.

Theorem subst_iff_count_nonzero : forall pre post t,
  count_free pre t = 0 <-> subst pre post t = Unused.
Proof. intros. rewrite reflect_not_subst. apply subst_iff_count_nonzero_prop. Qed.

Theorem reflect_subst : forall pre post t t',
  subst pre post t = Used t' <-> Subst pre post t t'.
Proof.
  split; intros.
  - generalize dependent pre. generalize dependent post. generalize dependent t'.
    induction t; intros; simpl in *; subst; invert H;
    [destruct (eqb pre id) eqn:E; [| discriminate]; rewrite eqb_eq in E; invert H1; constructor | | |];
    try (destruct arg; [destruct (eqb pre s) eqn:E; [discriminate H1 |]; rewrite eqb_neq in E |]);
    destruct (subst pre post t1) eqn:E1; try apply IHt1 in E1;
    destruct (subst pre post t2) eqn:E2; try apply IHt2 in E2;
    simpl in *; invert H1; constructor; try assumption;
    apply reflect_count_free; eapply subst_iff_count_nonzero; apply E1.
  - induction H; simpl in *; try rewrite eqb_refl; try rewrite <- eqb_neq in *; try rewrite IHSubst;
    try rewrite <- reflect_count_free in *; try erewrite subst_iff_count_nonzero in *;
    try rewrite H; try rewrite H0; reflexivity.
Qed.

(* TODO: Prove semantics are invariant to variable name changes! I'm not entirely sure `subst` is right. *)

(* Crucial theorem! *)
Theorem subst_exactly_once : forall pre post t t',
  count_free pre post = 0 ->
  subst pre post t = Used t' ->
  count_free pre t = S (count_free pre t').
Proof.
  intros pre post t t' Hc Hs. repeat rewrite <- count_free_eq in *. apply reflect_subst in Hs.
  induction Hs; simpl in *; try rewrite Hc; try rewrite IHHs;
  try rewrite eqb_refl in *; try rewrite Nat.add_succ_r in *;
  try rewrite <- eqb_neq in *; try rewrite H; reflexivity.
Qed.

(*
Ideally, we would have a model of `forall` that
naturally encoded the kind of linearity we want
under Church encodings like in the C.o.C.:
  - Arrow types are just anonymous `forall`s, so
    an easy unit test is that we shouldn't be able to
    reuse or ignore the argument of a `forall`.
    Use it exactly once, and that's it.
  - Next, (A, B) is represented ingeniously as
    `forall C: Prop, (A -> B -> C) -> C`, i.e.
    `forall C: Prop, forall _: (forall (_: A) (_: B), C), C`.
    I think this would naturally allow us to
    use each item exactly once as intended, but
    it deserves more thought and a formal proof.
*)
