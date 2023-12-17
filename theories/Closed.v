From Coq Require Export
  Lists.List.
Export ListNotations.
From Adam Require Import
  Invert
  OptionBind
  Snoc
  Terms
  Types.

(* Free variables under a given context (without types).
 * Returns all free variables in reverse order. *)
Fixpoint fv_under ctx acc t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ _ =>
      (ctx, acc)
  | TmVarS s =>
      match ctx with
      | hd :: tl => if eqb s hd then (tl, acc) else (ctx, s :: acc)
      | [] => (ctx, s :: acc)
      end
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b => 
      let (ctmp, atmp) := fv_under ctx acc a in
      fv_under ctmp atmp b
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry => 
      let (ctmp, atmp) := fv_under ctx acc ty in
      fv_under (arg :: ctmp) atmp curry
  end.
Definition fv : term -> list string := fun t => let (_, f) := fv_under [] [] t in f.
Arguments fv t/.
Definition closed : term -> bool := fun t => match fv t with [] => true | _ :: _ => false end.
Arguments closed t/.

Lemma fv_acc_app : forall ctx hd tl t c1 a1 c2 a2,
  fv_under ctx (hd ++ tl) t = (c1, a1) ->
  fv_under ctx (hd      ) t = (c2, a2) ->
  (c1 = c2 /\ a1 = a2 ++ tl).
Proof.
  intros ctx hd tl t. generalize dependent tl. generalize dependent hd. generalize dependent ctx.
  induction t; intros; simpl in *; invert H; invert H0; try solve [split; reflexivity].
  - destruct ctx. { invert H1. invert H2. split; reflexivity. }
    destruct (eqb id s) eqn:E; invert H1; invert H2; split; reflexivity.
  - destruct (fv_under ctx (hd ++ tl) t1) as [ctmp atmp] eqn:E1.
    destruct (fv_under ctx hd t1) as [ctmp' atmp'] eqn:E2.
    remember (IHt1 _ _ _ _ _ _ _ E1 E2) as H. destruct H. subst.
    destruct arg; apply (IHt2 _ _ _ _ _ _ _ H2 H1).
  - destruct (fv_under ctx (hd ++ tl) t1) as [ctmp atmp] eqn:E1.
    destruct (fv_under ctx hd t1) as [ctmp' atmp'] eqn:E2.
    remember (IHt1 _ _ _ _ _ _ _ E1 E2) as H. destruct H. subst.
    destruct arg; apply (IHt2 _ _ _ _ _ _ _ H2 H1).
  - destruct (fv_under ctx (hd ++ tl) t1) as [ctmp atmp] eqn:E1.
    destruct (fv_under ctx hd t1) as [ctmp' atmp'] eqn:E2.
    remember (IHt1 _ _ _ _ _ _ _ E1 E2) as H. destruct H. subst.
    apply (IHt2 _ _ _ _ _ _ _ H2 H1).
Qed.

(* WOOHOO!!!!!!!!!!!!!!!! *)

Lemma fv_acc_app_backward : forall ctx hd tl t c a,
  fv_under ctx hd t = (c, a) ->
  fv_under ctx (hd ++ tl) t = (c, a ++ tl).
Proof.
  intros. destruct (fv_under ctx (hd ++ tl) t) as [c' a'] eqn:E.
  eapply fv_acc_app in H; try apply E. destruct H. subst. reflexivity.
Qed.

Lemma fv_acc_app_forward : forall ctx hd tl t c a a',
  fv_under ctx (hd ++ tl) t = (c, a) ->
  a = a' ++ tl ->
  fv_under ctx hd t = (c, a').
Proof.
  intros ctx hd tl t c a a' Hf Ha. destruct (fv_under ctx hd t) eqn:E.
  assert (A := fv_acc_app _ _ _ _ _ _ _ _ Hf E). destruct A. subst.
  f_equal. symmetry. eapply app_inv_tail. apply H0.
Qed.

Inductive FVUnder : list string -> term -> list string -> list string -> Prop :=
  | FVUnderVoid : forall ctx,
      FVUnder ctx TmVoid ctx []
  | FVUnderStar : forall ctx lvl,
      FVUnder ctx (TmStar lvl) ctx []
  | FVUnderAtom : forall ctx id lvl,
      FVUnder ctx (TmAtom id lvl) ctx []
  | FVUnderVarSE : forall ctx x,
      FVUnder (x :: ctx) (TmVarS x) ctx []
  | FVUnderVarSD : forall ctx x,
      hd_error ctx <> Some x ->
      FVUnder ctx (TmVarS x) ctx [x]
  | FVUnderPackNone : forall ctx id ty curry c1 a1 c2 a2 a,
      FVUnder ctx ty c1 a1 ->
      FVUnder c1 curry c2 a2 ->
      a1 ++ a2 = a ->
      FVUnder ctx (TmPack id None ty curry) c2 a
  | FVUnderForANone : forall ctx ty curry c1 a1 c2 a2 a,
      FVUnder ctx ty c1 a1 ->
      FVUnder c1 curry c2 a2 ->
      a1 ++ a2 = a ->
      FVUnder ctx (TmForA None ty curry) c2 a
  | FVUnderAppl : forall ctx f x c1 a1 c2 a2 a,
      FVUnder ctx f c1 a1 ->
      FVUnder c1 x c2 a2 ->
      a1 ++ a2 = a ->
      FVUnder ctx (TmAppl f x) c2 a
  | FVUnderPackSome : forall ctx id arg ty curry c1 a1 c2 a2 a,
      FVUnder ctx ty c1 a1 ->
      FVUnder (arg :: c1) curry c2 a2 ->
      a1 ++ a2 = a ->
      FVUnder ctx (TmPack id (Some arg) ty curry) c2 a
  | FVUnderForASome : forall ctx arg ty curry c1 a1 c2 a2 a,
      FVUnder ctx ty c1 a1 ->
      FVUnder (arg :: c1) curry c2 a2 ->
      a1 ++ a2 = a ->
      FVUnder ctx (TmForA (Some arg) ty curry) c2 a
  .
Theorem reflect_fv_under : forall ctx t ctx' out,
  fv_under ctx [] t = (ctx', out) <-> FVUnder ctx t ctx' (rev out).
Proof.
  split; intros.
  - generalize dependent out. generalize dependent ctx'. generalize dependent ctx.
    induction t; intros; simpl in *; invert H; try constructor;
    [ destruct ctx; invert H1; [constructor; intro C; discriminate C |];
      destruct (eqb id s) eqn:E; [apply eqb_eq in E; invert H0; constructor |];
      invert H0; constructor; intro C; invert C; rewrite eqb_refl in E; discriminate E | | |];
    destruct (fv_under ctx [] t1) as [ctmp atmp] eqn:E; [| | destruct (fv_under ctmp [] t2) as [c' a'] eqn:E2];
    try (destruct arg; [
      destruct (fv_under (s :: ctmp) [] t2) as [c' a'] eqn:E2 |
      destruct (fv_under ctmp [] t2) as [c' a'] eqn:E2]);
    assert (A := fv_acc_app _ [] _ _ _ _ _ _ H1 E2); destruct A; subst;
    apply IHt1 in E; apply IHt2 in E2; econstructor; try apply E; try apply E2;
    rewrite rev_app_distr; reflexivity.
  - remember (rev out) as rout eqn:Er. generalize dependent out. induction H; intros; simpl in *;
    try (eapply f_equal in Er; rewrite rev_involutive in Er);
    subst; simpl in *; try rewrite eqb_refl; try reflexivity;
    [ destruct ctx; try reflexivity; destruct (eqb x s) eqn:E; try reflexivity;
      apply eqb_eq in E; subst; contradiction H; reflexivity | | | | |];
    specialize (IHFVUnder1 (rev a1)); rewrite rev_involutive in IHFVUnder1;
    specialize (IHFVUnder1 eq_refl); rewrite IHFVUnder1;
    try (
      destruct (fv_under (arg :: c1) (rev a1) curry) as [c a] eqn:E1;
      destruct (fv_under (arg :: c1) [] curry) as [c' a'] eqn:E2);
    try (
      destruct (fv_under c1 (rev a1) curry) as [c a] eqn:E1;
      destruct (fv_under c1 [] curry) as [c' a'] eqn:E2);
    try (
      destruct (fv_under c1 (rev a1) x) as [c a] eqn:E1;
      destruct (fv_under c1 [] x) as [c' a'] eqn:E2);
    assert (A := fv_acc_app _ [] _ _ _ _ _ _ E1 E2); destruct A; subst; rewrite rev_app_distr;
    specialize (IHFVUnder2 (rev a2)); rewrite rev_involutive in IHFVUnder2;
    specialize (IHFVUnder2 eq_refl); invert IHFVUnder2; reflexivity.
Qed.

Definition FreeVars := fun t v => exists ctx', FVUnder [] t ctx' v.
Definition Closed := fun t => FreeVars t [].
Arguments Closed t/.

Lemma map_distr : forall {A B} (f : A -> B) hd tl, map f (hd ++ tl) = map f hd ++ map f tl.
Proof.
  intros. generalize dependent tl. generalize dependent B.
  induction hd; intros; simpl in *; try rewrite IHhd; reflexivity.
Qed.

(*
Theorem typed_implies_closed : forall ctx t ty,
  Typed ctx t ty -> FVUnder (map fst ctx) t [] [].
Proof.
  intros. induction H; intros; simpl in *; subst; simpl in *;
  try discriminate; try solve [repeat econstructor].
  - rewrite map_distr. econstructor; try apply IHTyped2; try (rewrite app_nil_r; reflexivity).
    apply (reflect_fv_under _ _ _ []) in IHTyped1.
    destruct (fv_under (map fst ctxt) (map fst ctxc) ty) eqn:E.
    eapply fv_acc_app in IHTyped1; try apply E. destruct IHTyped1. subst.
  - destruct ctxt; destruct ctxc; try discriminate E.
    specialize (IHTyped1 eq_refl). specialize (IHTyped2 eq_refl).
    econstructor; try apply IHTyped1; try apply IHTyped2. reflexivity.
  - destruct ctxt; destruct ctxc; try discriminate E.
    specialize (IHTyped1 eq_refl).
    econstructor; try apply IHTyped1; try apply IH2. reflexivity.
    econstructor.
Qed.

Fixpoint binds vars (ctx : context) :=
  match vars, ctx with
  | [], [] => true
  | hv :: tv, (v, t) :: tc => if eqb hv v then binds tv tc else false
  | _, _ => false
  end.
Inductive Binds : list string -> context -> Prop :=
  | BindsNil : Binds [] []
  | BindsCons : forall v tv t tc,
      Binds tv tc ->
      Binds (v :: tv) ((v, t) :: tc)
  .
Theorem reflect_binds : forall vars ctx,
  binds vars ctx = true <-> Binds vars ctx.
Proof.
  split; intros.
  - generalize dependent ctx. induction vars; intros; simpl in *.
    + destruct ctx. { constructor. } discriminate H.
    + destruct ctx. { discriminate H. } destruct p. destruct (eqb a s) eqn:E; try discriminate H.
      apply eqb_eq in E. subst. constructor. apply IHvars. assumption.
  - induction H. { reflexivity. } simpl. rewrite eqb_refl. assumption.
Qed.

(* extremely strict correctness guarantee *)
Theorem typed_iff_binds_fv : forall ctx t ty,
  Typed ctx t ty ->
  Binds (rev (fv t)) ctx.
Proof.
  (*
  intros ctx. induction ctx; intros; simpl in *.
  - remember [] as ctx eqn:Ectx. induction H; intros; subst; simpl in *; try discriminate; repeat constructor.
    + destruct ctxt; try discriminate H1. simpl in *. subst. simpl in *.
      destruct (fv_under [] [] ty) eqn:E. specialize (IHTyped1 eq_refl). specialize (IHTyped2 eq_refl).
      invert IHTyped1. eapply f_equal in H3. rewrite rev_involutive in H3. subst. simpl in *.
  *)
  intros. induction H; intros; simpl in *; try solve [repeat constructor].
  - destruct (fv_under [] []) as [ctmp atmp] eqn:Ef1. invert H2.
    + invert IHTyped2. invert H0. rewrite app_nil_r. destruct (fv_under [] [] ty). assumption.
    + destruct (fv_under [] [] ty) as [ctmp atmp] eqn:Ef. invert H0. simpl in *.
  - generalize dependent ctx. generalize dependent ctxt. generalize dependent ctxc.
    generalize dependent ty. generalize dependent t. generalize dependent kind.
    induction H2; intros; simpl in *.
    + invert IHTyped2. invert H0. rewrite app_nil_r. destruct (fv_under [] [] ty). assumption.
    + invert H0.
      * clear IHAtomId; clear IHTyped2. try apply H10. admit.
      * destruct (fv_under [] [] ty0) as [ctmp atmp] eqn:Ef1.
        destruct (fv_under ctmp atmp ty) as [ctmp' atmp'] eqn:Ef2.
        destruct (fv_under ctmp' atmp' curry) as [ctmp'' atmp''] eqn:Ef3.
        eapply IHAtomId in H10. clear IHAtomId; clear IHTyped2. invert H0.
      destruct (fv_under [] [] ty0). destruct (fv_under l l0 ty). invert H0. eapply IHAtomId in H10; clear IHAtomId.
    inversion IHTyped; subst; simpl in *.
    + eapply f_equal in H2. rewrite rev_involutive in H2. simpl in *.
      destruct (fv_under [] [] curry). clear l. subst.
Qed.

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

Example bound_not_free : forall x, count_free x (TmForA (Some x) TmVoid (TmVarS x)) = 0.
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example free_used_twice : forall x, count_free x (TmForA (Some x) TmVoid (TmAppl (TmVarS x) (TmVarS x))) <> 0.
Proof. intros. simpl. rewrite eqb_refl.

Definition Closed : term -> Prop := fun t => forall x, CountFree x t 0.
Arguments Closed t/.

Fixpoint closed_under ctx t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ _ =>
      Some ctx
  | TmVarS s =>
      match ctx with hd :: tl => if eqb s hd then Some tl else None | [] => None end
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b => 
      option_bind (fun tmp => closed_under tmp b) (closed_under ctx a)
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry => 
      option_bind (fun tmp => closed_under (arg :: tmp) curry) (closed_under ctx ty)
  end.
Definition closed : term -> bool := fun t => match closed_under [] t with Some _ => true | None => false end.
Arguments closed t/.

Theorem closed_prop_implies_fix : forall t,
  Closed t -> closed t = true.
Proof.
  induction t; intros; simpl in *; try reflexivity.
  - specialize (H id). invert H. contradiction H1. reflexivity.
  - destruct arg.
    + destruct (closed_under [] t1) eqn:Ec.
      * admit.
      * apply IHt1. intros. specialize (H x). inversion H; subst. invert H.
Qed.

Theorem reflect_closed : forall t,
  closed t = true <-> Closed t.
Proof.
  split.
  - induction t; simpl in *; intros; try discriminate; try solve [constructor].
    + destruct arg; destruct (closed_under [] t1) eqn:E1; try discriminate H;
      [destruct (closed_under (s :: l) t2) eqn:E2 | destruct (closed_under l t2) eqn:E2];
      try discriminate H.
      * destruct (eqb x s) eqn:E. { apply eqb_eq in E. subst. constructor. } apply eqb_neq in E.
        econstructor; try assumption; try apply (IHt1 eq_refl); try apply IHt2; try reflexivity.
        admit.
      * econstructor; try apply (IHt1 eq_refl); try apply IHt2; try reflexivity.
    + destruct (closed_under [] t1) eqn:E1; destruct arg; try discriminate H;
      [destruct (closed_under (s :: l) t2) eqn:Ec | destruct (closed_under l t2) eqn:Ec]; try discriminate H;
      destruct l0; try discriminate H.
      * destruct (eqb x s) eqn:E. { apply eqb_eq in E. subst. econstructor. }
        apply eqb_neq in E. destruct l; econstructor; try assumption.
        econstructor; try assumption. destruct l.
  - induction t; intros; simpl in *.
Qed.
*)
