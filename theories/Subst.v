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

(* Resource-aware substitution: substitute exactly once. *)
(* TODO: Prove the above. *)
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
Inductive Subst (pre : string) (post : term) : term -> resource term -> Prop :=
  | SubstVoid :
      Subst pre post TmVoid Unused
  | SubstStar : forall lvl,
      Subst pre post (TmStar lvl) Unused
  | SubstVarE :
      Subst pre post (TmVarS pre) (Used post)
  | SubstVarD : forall id,
      pre <> id ->
      Subst pre post (TmVarS id) Unused
  | SubstAtom : forall id lvl,
      Subst pre post (TmAtom id lvl) Unused
  | SubstPackAlias : forall id ty curry,
      Subst pre post (TmPack id (Some pre) ty curry) Unused
  | SubstPackNoneL : forall id ty ty' curry,
      Subst pre post ty (Used ty') ->
      Subst pre post (TmPack id None ty curry) (Used (TmPack id None ty' curry))
  | SubstPackNoneR : forall id ty curry curry',
      Subst pre post ty Unused ->
      Subst pre post curry (Used curry') ->
      Subst pre post (TmPack id None ty curry) (Used (TmPack id None ty curry'))
  | SubstPackNoneA : forall id ty curry,
      Subst pre post ty Unused ->
      Subst pre post curry Unused ->
      Subst pre post (TmPack id None ty curry) Unused
  | SubstPackSomeL : forall id arg ty ty' curry,
      pre <> arg ->
      Subst pre post ty (Used ty') ->
      Subst pre post (TmPack id (Some arg) ty curry) (Used (TmPack id (Some arg) ty' curry))
  | SubstPackSomeR : forall id arg ty curry curry',
      pre <> arg ->
      Subst pre post ty Unused ->
      Subst pre post curry (Used curry') ->
      Subst pre post (TmPack id (Some arg) ty curry) (Used (TmPack id (Some arg) ty curry'))
  | SubstPackSomeA : forall id arg ty curry,
      pre <> arg ->
      Subst pre post ty Unused ->
      Subst pre post curry Unused ->
      Subst pre post (TmPack id (Some arg) ty curry) Unused
  | SubstForAAlias : forall ty body,
      Subst pre post (TmForA (Some pre) ty body) Unused
  | SubstForANoneL : forall ty ty' body,
      Subst pre post ty (Used ty') ->
      Subst pre post (TmForA None ty body) (Used (TmForA None ty' body))
  | SubstForANoneR : forall ty body body',
      Subst pre post ty Unused ->
      Subst pre post body (Used body') ->
      Subst pre post (TmForA None ty body) (Used (TmForA None ty body'))
  | SubstForANoneA : forall ty body,
      Subst pre post ty Unused ->
      Subst pre post body Unused ->
      Subst pre post (TmForA None ty body) Unused
  | SubstForASomeL : forall arg ty ty' body,
      pre <> arg ->
      Subst pre post ty (Used ty') ->
      Subst pre post (TmForA (Some arg) ty body) (Used (TmForA (Some arg) ty' body))
  | SubstForASomeR : forall arg ty body body',
      pre <> arg ->
      Subst pre post ty Unused ->
      Subst pre post body (Used body') ->
      Subst pre post (TmForA (Some arg) ty body) (Used (TmForA (Some arg) ty body'))
  | SubstForASomeA : forall arg ty body,
      pre <> arg ->
      Subst pre post ty Unused ->
      Subst pre post body Unused ->
      Subst pre post (TmForA (Some arg) ty body) Unused
  | SubstApplL : forall f f' x,
      Subst pre post f (Used f') ->
      Subst pre post (TmAppl f x) (Used (TmAppl f' x))
  | SubstApplR : forall f x x',
      Subst pre post f Unused ->
      Subst pre post x (Used x') ->
      Subst pre post (TmAppl f x) (Used (TmAppl f x'))
  | SubstApplA : forall f x,
      Subst pre post f Unused ->
      Subst pre post x Unused ->
      Subst pre post (TmAppl f x) Unused
  .
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
Theorem reflect_subst : forall pre post t r,
  subst pre post t = r <-> Subst pre post t r.
Proof.
  split; intros.
  - generalize dependent pre. generalize dependent post. generalize dependent r.
    induction t; intros; simpl in *; subst;
    try constructor; try apply IHt1; try apply IHt2; try reflexivity.
    + destruct (eqb pre id) eqn:E.
      * rewrite eqb_eq in E. subst. constructor.
      * rewrite eqb_neq in E. constructor. assumption.
    + destruct arg.
      * destruct (eqb pre s) eqn:E.
        -- rewrite eqb_eq in E. subst. constructor.
        -- rewrite eqb_neq in E.
           destruct (subst pre post t1) eqn:E1; apply IHt1 in E1;
           destruct (subst pre post t2) eqn:E2; apply IHt2 in E2;
           constructor; assumption.
      * destruct (subst pre post t1) eqn:E1; apply IHt1 in E1;
        destruct (subst pre post t2) eqn:E2; apply IHt2 in E2;
        constructor; assumption.
    + destruct arg.
      * destruct (eqb pre s) eqn:E.
        -- rewrite eqb_eq in E. subst. constructor.
        -- rewrite eqb_neq in E.
           destruct (subst pre post t1) eqn:E1; apply IHt1 in E1;
           destruct (subst pre post t2) eqn:E2; apply IHt2 in E2;
           constructor; assumption.
      * destruct (subst pre post t1) eqn:E1; apply IHt1 in E1;
        destruct (subst pre post t2) eqn:E2; apply IHt2 in E2;
        constructor; assumption.
    + destruct (subst pre post t1) eqn:E1; apply IHt1 in E1;
      destruct (subst pre post t2) eqn:E2; apply IHt2 in E2;
      constructor; assumption.
  - induction H; simpl in *; subst; try rewrite eqb_refl;
    try destruct (eqb pre arg) eqn:E;
    try rewrite eqb_eq in E; subst; try (contradiction H; reflexivity);
    try apply eqb_neq in H; try rewrite H; try rewrite IHSubst;
    try rewrite IHSubst1; try rewrite IHSubst2; try reflexivity.
Qed.

(* TODO: Prove semantics are invariant to variable name changes! I'm not entirely sure `subst` is right. *)

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

Theorem subst_iff_at_least_one : forall pre post t,
  count_free pre t = 0 <-> subst pre post t = Unused.
Proof.
  intros. rewrite reflect_count_free. rewrite reflect_subst. split; intros.
  - remember 0 as n eqn:En. induction H; intros; simpl in *; invert En; constructor;
    try destruct a; try destruct b; try discriminate H1; try discriminate H2;
    try apply IHCountFree1; try apply IHCountFree2; assumption.
  - remember Unused as r eqn:Er. induction H; invert Er; simpl in *; econstructor;
    try assumption; try apply IHSubst1; try apply IHSubst2; reflexivity.
Qed.

(* Crucial theorem! *)
Theorem subst_exactly_once : forall pre post t t',
  subst pre post t = Used t' ->
  count_free pre t = S (count_free pre t').
Proof.
  intros pre post t. generalize dependent pre. generalize dependent post.
  induction t; intros; try discriminate H.
  - simpl in *. destruct (eqb pre id). invert H1.

  intros. rewrite reflect_subst in H. remember (Used t') as r eqn:Er. generalize dependent t'.
  induction H; intros; simpl in *; try discriminate Er.

  intros. remember (count_free pre t') as n eqn:En. symmetry in En.
  rewrite reflect_subst in H. repeat rewrite reflect_count_free in *.
  generalize dependent n. remember (Used t') as r eqn:Er.
  induction H; intros; simpl in *; try discriminate Er.
  - invert Er. constructor.
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
