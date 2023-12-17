From Coq Require Export
  Lists.List.
Export ListNotations.
From Adam Require Import
  Invert
  OptionBind
  Snoc
  Terms
  Types.

(*
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
*)

Fixpoint fv_slow t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ _ =>
      []
  | TmVarS s =>
      [s]
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      fv_slow a ++ fv_slow b
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      fv_slow ty ++
      match fv_slow curry with
      | [] => []
      | hd :: tl => if eqb arg hd then tl else hd :: tl
      end
  end.
Fixpoint fv_fast acc t :=
  match t with
  | TmVoid
  | TmStar _
  | TmAtom _ _ =>
      acc
  | TmVarS s =>
      s :: acc
  | TmPack _ None a b
  | TmForA None a b
  | TmAppl a b =>
      fv_fast (fv_fast acc b) a
  | TmPack _ (Some arg) ty curry
  | TmForA (Some arg) ty curry =>
      match fv_fast (fv_fast acc curry) ty with
      | [] => []
      | hd :: tl => if eqb arg hd then tl else hd :: tl
      end
  end.

Lemma fv_fast_acc_app : forall acc t,
  fv_fast acc t = fv_fast [] t ++ acc.
Proof.
  intros. generalize dependent acc. induction t; intros; simpl in *;
  simpl in *; try reflexivity.
  - destruct arg; rewrite IHt1; rewrite (IHt1 (fv_fast [] t2)); rewrite IHt2; [| rewrite app_assoc; reflexivity].
    (* FUCK *) Abort.

(*
Theorem fv_fast_slow_eq : forall t,
  fv t = fv_slow t.
Proof.
  unfold fv. intros. induction t; intros; simpl in *;
  try rewrite IHt1; try rewrite IHt2; simpl in *; try reflexivity.
Qed.

Definition fv := fv_fast [].
*)

Definition fv := fv_slow.

Example fv_respects_scope : forall x,
  (* Equivalent to `(\x:0. 0) x`, in which the outer `x` is still free *)
  fv (TmAppl (TmForA (Some x) TmVoid TmVoid) (TmVarS x)) = [x].
Proof. intros. simpl. reflexivity. Qed.

Inductive FreeIn : term -> list string -> Prop :=
  | FreeVoid :
      FreeIn TmVoid []
  | FreeStar : forall lvl,
      FreeIn (TmStar lvl) []
  | FreeAtom : forall id lvl,
      FreeIn (TmAtom id lvl) []
  | FreeVarS : forall x,
      FreeIn (TmVarS x) [x]
  | FreePackNone : forall id ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      FreeIn (TmPack id None ty curry) v
  | FreeForANone : forall ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      FreeIn (TmForA None ty curry) v
  | FreeAppl : forall f x va vb v,
      FreeIn f va ->
      FreeIn x vb ->
      va ++ vb = v ->
      FreeIn (TmAppl f x) v
  | FreePackMatch : forall id arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry (arg :: vb) ->
      va ++ vb = v ->
      FreeIn (TmPack id (Some arg) ty curry) v
  | FreeForAMatch : forall arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry (arg :: vb) ->
      va ++ vb = v ->
      FreeIn (TmForA (Some arg) ty curry) v
  | FreePackDiff : forall id arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      hd_error vb <> Some arg ->
      FreeIn (TmPack id (Some arg) ty curry) v
  | FreeForADiff : forall arg ty curry va vb v,
      FreeIn ty va ->
      FreeIn curry vb ->
      va ++ vb = v ->
      hd_error vb <> Some arg ->
      FreeIn (TmForA (Some arg) ty curry) v
  .

Definition Closed := fun t => FreeIn t [].
Arguments Closed t/.

Lemma map_distr : forall {A B} (f : A -> B) hd tl, map f (hd ++ tl) = map f hd ++ map f tl.
Proof.
  intros. generalize dependent tl. generalize dependent B.
  induction hd; intros; simpl in *; try rewrite IHhd; reflexivity.
Qed.

(* Fantastic that we can prove something this precise! *)
Theorem typed_requires_fv : forall ctx t ty,
  Typed ctx t ty -> FreeIn t (map fst ctx).
Proof.
  intros. induction H; intros; simpl in *; subst; econstructor;
  try apply IHTyped1; try apply IHTyped2; rewrite <- map_distr; reflexivity.
Qed.

Theorem reflect_fv : forall t v,
  FreeIn t v <-> fv t = v.
Proof.
  split; intros.
  - induction H; intros; simpl in *; subst; try rewrite IHFreeIn2; try rewrite eqb_refl; try reflexivity;
    destruct (fv curry); try reflexivity; destruct (eqb arg s) eqn:E; try reflexivity;
    rewrite eqb_eq in E; subst; contradiction H2; reflexivity.
  - generalize dependent v. induction t; intros; simpl in *; subst; try solve [econstructor].
    + destruct arg; try (econstructor; try apply IHt1; try apply IHt2; reflexivity). destruct (fv t2).
      { eapply FreePackDiff; try apply IHt1; try apply IHt2; try reflexivity. intro C. discriminate C. }
      destruct (eqb s s0) eqn:E.
      * apply eqb_eq in E. subst. econstructor; try apply IHt1; try apply IHt2; reflexivity.
      * apply eqb_neq in E. eapply FreePackDiff; try apply IHt1; try apply IHt2; try reflexivity.
        intro C. simpl in C. invert C. contradiction E. reflexivity.
    + destruct arg; try (econstructor; try apply IHt1; try apply IHt2; reflexivity). destruct (fv t2).
      { eapply FreeForADiff; try apply IHt1; try apply IHt2; try reflexivity. intro C. discriminate C. }
      destruct (eqb s s0) eqn:E.
      * apply eqb_eq in E. subst. econstructor; try apply IHt1; try apply IHt2; reflexivity.
      * apply eqb_neq in E. eapply FreeForADiff; try apply IHt1; try apply IHt2; try reflexivity.
        intro C. simpl in C. invert C. contradiction E. reflexivity.
    + econstructor; try apply IHt1; try apply IHt2; reflexivity.
Qed.

Theorem fv_not_typed : forall t,
  fv t <> [] -> ~exists ty, Typed [] t ty.
Proof.
  intros t H [ty C]. apply typed_requires_fv in C. apply reflect_fv in C.
  rewrite C in H. contradiction H. reflexivity.
Qed.
