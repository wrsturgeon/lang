From Coq Require Export
  Lists.List
  Sorting.Permutation.
Export ListNotations.
From Lang Require Import
  Invert
  Subst
  Terms.

Definition context : Set := list (string * term).
Arguments context/.

Definition judgment : Type := context -> term -> term -> Prop.
Arguments judgment/.

Inductive WithWeakening (P : judgment) : judgment :=
  | WeakSkip : forall hd tl t t',
      WithWeakening P tl t t' ->
      WithWeakening P (hd :: tl) t t'
  | WeakOrig : forall ctx t t',
      P ctx t t' ->
      WithWeakening P ctx t t'
  .

Inductive WithContraction (P : judgment) : judgment :=
  | CntrCopy : forall hd tl t t',
      WithContraction P (hd :: hd :: tl) t t' ->
      WithContraction P (hd :: tl) t t'
  | CntrOrig : forall ctx t t',
      P ctx t t' ->
      WithContraction P ctx t t'
  .

Inductive WithExchange (P : judgment) : judgment :=
  | ExchPerm : forall ctx1 ctx2 t t',
      WithExchange P ctx2 t t' ->
      Permutation ctx1 ctx2 ->
      WithExchange P ctx1 t t'
  | ExchOrig : forall ctx t t',
      P ctx t t' ->
      WithExchange P ctx t t'
  .

(* Typed extremely strictly, as if on a stack: no exchange, no weakening, no contraction. *)
Print term.
Inductive Typed : context -> term -> term -> Prop :=
  | TyVarS : forall id t,
      Typed [(id, t)] (TmVarS id) t
  | TyAtom : forall id,
      Typed [] (TmAtom id) (TmAtom id)
  | TyPack : forall ctx ctxt ctxc id arg ty curry t kind,
      Typed ctxt ty kind ->
      Typed (match arg with Some x => (x, ty) :: ctxc | None => ctxc end) curry t ->
      ctxt ++ ctxc = ctx ->
      AtomId id curry ->
      Typed ctx (TmPack id arg ty curry) (TmForA arg ty t)
  | TyForA : forall ctx ctxt ctxc arg ty body t kind,
      Typed ctxt ty kind ->
      Typed (match arg with Some x => (x, ty) :: ctxc | None => ctxc end) body t ->
      ctxt ++ ctxc = ctx ->
      Typed ctx (TmForA arg ty body) (TmForA arg ty t)
  | TyApplNone : forall ctx ctxf ctxx f x ty body,
      Typed ctxf f (TmForA None ty body) ->
      Typed ctxx x ty ->
      ctx = ctxf ++ ctxx ->
      Typed ctx (TmAppl f x) body
  | TyApplSome : forall ctx ctxf ctxx f x arg ty body sub,
      Typed ctxf f (TmForA (Some arg) ty body) ->
      Typed ctxx x ty ->
      ctx = ctxf ++ ctxx ->
      subst arg x body = Some sub ->
      Typed ctx (TmAppl f x) sub
  | TyStar : forall ctx t ty,
      Typed ctx t ty ->
      Typed ctx t TmStar
  .

(* TODO: CRUCIAL SAFETY THEOREMS: (1) Star does not have type Star, and (2) no term has type Void *)

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
Proof. simpl. eapply TyApplNone. { apply TyVarS. } { apply TyVarS. } reflexivity. Qed.

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
  intros [t C]. invert C.
  - invert H3. repeat (destruct ctxf; try discriminate H5). invert H5. invert H1.
    + invert H4. repeat (destruct ctxf; try discriminate H6).
    + invert H3. repeat (destruct ctxf; try discriminate H5).
  - invert H2. repeat (destruct ctxf; try discriminate H4). invert H4. invert H1.
    + invert H4. repeat (destruct ctxf; try discriminate H7).
    + invert H3. repeat (destruct ctxf; try discriminate H5).
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
  WithExchange (WithContraction (WithExchange Typed)) ctx fxx Y.
Proof.
  simpl.
  eapply ExchPerm. apply ExchOrig. (* Move `x` to the front *)
  apply CntrCopy. apply CntrOrig. (* Copy it *)
  eapply ExchPerm. apply ExchOrig. (* Move both to the back again *)
  repeat econstructor. (* This does a LOT of work for us; now only permutations left *)
  - simpl. eapply perm_trans. { eapply perm_trans. { apply perm_skip. apply perm_swap. } apply perm_swap. }
    repeat apply perm_skip. apply perm_nil.
  - apply perm_swap.
Qed.

(* TODO: Maybe take an argument in `Typed` that represents the typing relation in hypotheses,
 * so we don't have to nest structural rules like above. *)

(* NOTE: If we can type all functions s.t. output type represents only actual possible outputs,
   then we should be able to prove that all arrow types have an input type size
   greater than or equal to its output type size!
   Dizzying implications in terms of what a program has to start with--TODO: figure this out.
   This might be a crucial lemma in proving type safety (since a void output implies void input)! *)

(* Fantastic that we can prove something this precise! *)
Theorem typed_requires_fv : forall ctx t ty,
  Typed ctx t ty -> FreeIn t (map fst ctx).
Proof.
  intros. induction H; intros; simpl in *; subst; econstructor;
  try apply IHTyped1; try apply IHTyped2; rewrite <- map_distr; reflexivity.
Qed.

Theorem fv_not_typed : forall t,
  fv t <> [] -> ~exists ty, Typed [] t ty.
Proof.
  intros t H [ty C]. apply typed_requires_fv in C. apply reflect_fv in C.
  rewrite C in H. contradiction H. reflexivity.
Qed.
