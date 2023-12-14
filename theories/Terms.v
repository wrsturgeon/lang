From Coq Require Export
  Strings.String.
Export PeanoNat.

(* What are atoms?
 * Atoms are trivial, user-created terms whose types are themselves.
 * Importantly, nothing but themselves can have themselves as a type.
 * So let's define one. Say we want to represent Boolean values.
 * We'd define an atom `true`, whose type is `true`.
 * Furthermore, we know that no other term has type `true`,
 * so if we're a function and we get a value of type `true`,
 * we know precisely what it is without having to check.
 * Next, we'd create a *separate* atom called `false` (of type `false`).
 * Notice how this is different from other languages:
 * e.g. in Haskell, we'd define a `data`-type called `boolean`,
 * and we'd relate this one type to multiple constructors.
 * Here, we don't do that: types and constructors are one-to-one.
 * Instead, we define `boolean` as an _expression_ involving types:
 * `boolean = true | false`. So `boolean` has two values.
 *
 * So, why on Earth would this twisted thinking be valuable?
 * First, when we get a value of type `true | false`,
 * we can read directly off the type
 * exactly how many values it could be.
 * In this case, there can only be two,
 * so we need only log_2(2) = 1 bit of information.
 * And, crucially, if we're compiling a program you wrote,
 * and we see that some function always returns `true`,
 * we can literally remove `false` from the return type,
 * which might, for example, completely eliminate a
 * branch of a `match` statement down the line,
 * which might result in significantly reduced binary size,
 * not to mention fewer comparisons at runtime:
 * both necessarily make your programs run faster, and
 * both are not only nice but often crucial in low-level systems.
 *
 * Technical details:
 * Atoms should be able to take arguments (i.e., hold "members").
 * Doing this naively doesn't work: for example,
 * take a constructor `id` taking a natural-number argument.
 * You can't then admit a typing judgment `id : nat -> id`
 * unless typing rules change to allow
 * `(id @ 0) : nat -> (id @ 1)` and
 * `(id @ 1) : (id @ 2)` (identically for all n>1),
 * separately, which feels odd:
 * it breaks the whole idea of lowering types to evaluate them,
 * since types at different levels have different shapes entirely.
 * On the other hand, if we define types now without arguments,
 * then introduce arguments only as a side-effect of
 * Curry-encoded products instead of as a first-class construct,
 * defining a constructor "carrying" a `nat` would be no different than
 * a user-defined function from a `nat` to that constructor,
 * and we could just as easily define a function from a
 * different type to that constructor, which would type just fine.
 * Third, not a strategy but a constraint we want to uphold:
 * we need to consider unevaluated applications
 * _values_ if the application is a valid constructor carrying data.
 * The expression can't reduce any further, since
 * there is no "definition" to unfold as in a regular function,
 * so as it stands in the second strategy above,
 * we would immediately break the progress lemma.
 * Vague idea to allow unevaluated applications in the *type*,
 * instead of arrow types, to distinguish the two here.
 * Okay, here's an edit to the first strategy that I think might work:
 * Instead of what I said on the second line about
 * `(id @ 1) : (id @ 2)` and so on, just have,
 * for each level `i`, `(id @ i) : ... args ... -> (id @ (i + 1))`.
 * I think this might work. Gonna give it a shot.
 *)
Inductive term : Set :=
    (* Type with no constructors. *)
  | TmVoid
    (* Any term under (STRICTLY under) this universe level. *)
  | TmStar (lvl : nat)
    (* Variable, by name. *)
  | TmVarS (id : string)
    (* Atom with no arguments. *)
  | TmAtom (id : string) (lvl : nat)
    (* Atom with arguments (via currying). *)
  | TmPack (id : string) (arg : option string) (ty : term) (curry : term)
    (* Lambda abstraction, i.e. for-all statement. *)
  | TmForA (arg : option string) (ty : term) (body : term)
    (* Function (or atom with arguments) application. *)
  | TmAppl (f : term) (x : term)
  .

(* TODO: What if levels weren't stored here--
since typing is invariant to increments and decrements,
we could just store types at the same level as their terms,
then lazily bump them up during analysis in effect only--
instead, what if we only cared when taking a type argument? *)

Inductive AtomId id : term -> Prop :=
  | AtomIdAtom : forall lvl, AtomId id (TmAtom id lvl)
  | AtomIdPack : forall arg ty curry,
      AtomId id curry ->
      AtomId id (TmPack id arg ty curry)
  .

Definition eq_opt := fun lhs rhs =>
  match lhs, rhs with
  | None, None => true
  | Some a, Some b => eqb a b
  | _, _ => false
  end.
Theorem eq_opt_refl : forall x, eq_opt x x = true. Proof. intros []; [| reflexivity]. apply eqb_refl. Qed.
Theorem reflect_eq_opt : forall lhs rhs,
  eq_opt lhs rhs = true <-> lhs = rhs.
Proof.
  split; intros; [| subst; destruct rhs; try apply eqb_refl; reflexivity].
  destruct lhs; destruct rhs; try discriminate H; [| reflexivity].
  simpl in H. apply eqb_eq in H. subst. reflexivity.
Qed.

Fixpoint eq_term lhs rhs :=
  match lhs, rhs with
  | TmVoid, TmVoid => true
  | TmStar a, TmStar b => Nat.eqb a b
  | TmVarS a, TmVarS b => eqb a b
  | TmAtom idl lvll, TmAtom idr lvlr => andb (eqb idl idr) (Nat.eqb lvll lvlr)
  | TmPack idl argl tyl curryl, TmPack idr argr tyr curryr => andb (andb (andb
      (eqb idl idr)
      (eq_opt argl argr))
      (eq_term tyl tyr))
      (eq_term curryl curryr)
  | TmForA argl tyl bodyl, TmForA argr tyr bodyr => andb (andb
      (eq_opt argl argr)
      (eq_term tyl tyr))
      (eq_term bodyl bodyr)
  | TmAppl fl xl, TmAppl fr xr => andb (eq_term fl fr) (eq_term xl xr)
  | _, _ => false
  end.
Theorem eq_term_refl : forall t,
  eq_term t t = true.
Proof.
  induction t; simpl in *; repeat rewrite eqb_refl; repeat rewrite eq_opt_refl; repeat rewrite Nat.eqb_refl;
  repeat rewrite IHt1; repeat rewrite IHt2; try reflexivity.
Qed.
Theorem reflect_eq_term : forall lhs rhs,
  eq_term lhs rhs = true <-> lhs = rhs.
Proof.
  split; intros.
  - generalize dependent rhs. induction lhs; intros; simpl in *;
    destruct rhs; try discriminate H; repeat rewrite Bool.andb_true_iff in *;
    repeat rewrite eqb_eq in *; repeat rewrite reflect_eq_opt in *; repeat rewrite Nat.eqb_eq in *;
    repeat (subst; try reflexivity; destruct H);
    try apply IHlhs1 in H1; try apply IHlhs2 in H0; subst; try reflexivity.
    f_equal. apply IHlhs1. reflexivity.
  - subst. apply eq_term_refl.
Qed.

Inductive TermContains (needle : term) : term -> Prop :=
  | TmContainsRefl :
      TermContains needle needle
  | TmContainsPackTy : forall id arg ty curry,
      TermContains needle ty ->
      TermContains needle (TmPack id arg ty curry)
  | TmContainsPackCurry : forall id arg ty curry,
      TermContains needle curry ->
      TermContains needle (TmPack id arg ty curry)
  | TmContainsForATy : forall arg ty body,
      TermContains needle ty ->
      TermContains needle (TmForA arg ty body)
  | TmContainsForABody : forall arg ty body,
      TermContains needle body ->
      TermContains needle (TmForA arg ty body)
  | TmContainsApplF : forall f x,
      TermContains needle f ->
      TermContains needle (TmAppl f x)
  | TmContainsApplX : forall f x,
      TermContains needle x ->
      TermContains needle (TmAppl f x)
  .
Arguments TermContains needle haystack.
Fixpoint term_contains needle haystack :=
  orb (eq_term needle haystack)
  match haystack with
  | TmPack _ _ a b | TmForA _ a b | TmAppl a b =>
      orb (term_contains needle a) (term_contains needle b)
  | _ => false
  end.
Theorem term_contains_refl : forall t,
  term_contains t t = true.
Proof.
  intros []; simpl; repeat rewrite eqb_refl; repeat rewrite Nat.eqb_refl;
  repeat rewrite eq_opt_refl; repeat rewrite eq_term_refl; reflexivity.
Qed.
Theorem reflect_term_contains : forall needle haystack,
  term_contains needle haystack = true <-> TermContains needle haystack.
Proof.
  split; intros.
  - generalize dependent needle. induction haystack; intros; simpl in *;
    try rewrite Bool.orb_false_r in H; repeat (apply Bool.orb_prop in H; destruct H as [H | H]);
    try rewrite reflect_eq_term in H; subst; constructor;
    try apply IHhaystack1; try apply IHhaystack2; assumption.
  - induction H; simpl in *; try rewrite IHTermContains;
    repeat (simpl; rewrite Bool.orb_true_r); try reflexivity.
    apply term_contains_refl.
Qed.

Inductive TermContainsTerm (needle : term) : term -> Prop :=
  | TmContainsTmRefl :
      TermContainsTerm needle needle
  | TmContainsTmPack : forall id arg ty curry,
      TermContainsTerm needle curry ->
      TermContainsTerm needle (TmPack id arg ty curry)
  | TmContainsTmForA : forall arg ty body,
      TermContainsTerm needle body ->
      TermContainsTerm needle (TmForA arg ty body)
  | TmContainsTmApplF : forall f x,
      TermContainsTerm needle f ->
      TermContainsTerm needle (TmAppl f x)
  | TmContainsTmApplX : forall f x,
      TermContainsTerm needle x ->
      TermContainsTerm needle (TmAppl f x)
  .
Arguments TermContainsTerm needle haystack.
Fixpoint term_contains_term needle haystack :=
  orb (eq_term needle haystack)
  match haystack with
  | TmPack _ _ _ x | TmForA _ _ x => term_contains_term needle x
  | TmAppl a b =>
      orb (term_contains_term needle a) (term_contains_term needle b)
  | _ => false
  end.
Theorem term_contains_term_refl : forall t,
  term_contains_term t t = true.
Proof.
  intros []; simpl; repeat rewrite eqb_refl; repeat rewrite Nat.eqb_refl;
  repeat rewrite eq_opt_refl; repeat rewrite eq_term_refl; reflexivity.
Qed.
Theorem reflect_term_contains_term : forall needle haystack,
  term_contains_term needle haystack = true <-> TermContainsTerm needle haystack.
Proof.
  split; intros.
  - generalize dependent needle. induction haystack; intros; simpl in *;
    try rewrite Bool.orb_false_r in H; repeat (apply Bool.orb_prop in H; destruct H as [H | H]);
    try rewrite reflect_eq_term in H; subst; constructor;
    try apply IHhaystack1; try apply IHhaystack2; assumption.
  - induction H; simpl in *; try rewrite IHTermContainsTerm;
    repeat (simpl; rewrite Bool.orb_true_r); try reflexivity.
    apply term_contains_term_refl.
Qed.

Fixpoint map_levels f t :=
  match t with
  | TmVoid => TmVoid
  | TmStar lvl => TmStar (f lvl)
  | TmVarS id => TmVarS id
  | TmAtom id lvl => TmAtom id (f lvl)
  | TmPack id arg ty curry => TmPack id arg (map_levels f ty) (map_levels f curry)
  | TmForA id ty body => TmForA id (map_levels f ty) (map_levels f body)
  | TmAppl g x => TmAppl (map_levels f g) (map_levels f x)
  end.
Inductive MapLevels (F : nat -> nat -> Prop) : term -> term -> Prop :=
  | MapLvlVoid :
      MapLevels F TmVoid TmVoid
  | MapLvlStar : forall lvl lvl',
      F lvl lvl' ->
      MapLevels F (TmStar lvl) (TmStar lvl')
  | MapLvlVarS : forall id,
      MapLevels F (TmVarS id) (TmVarS id)
  | MapLvlAtom : forall id lvl lvl',
      F lvl lvl' ->
      MapLevels F (TmAtom id lvl) (TmAtom id lvl')
  | MapLvlPack : forall id arg ty ty' curry curry',
      MapLevels F ty ty' ->
      MapLevels F curry curry' ->
      MapLevels F (TmPack id arg ty curry) (TmPack id arg ty' curry')
  | MapLvlForA : forall id ty ty' body body',
      MapLevels F ty ty' ->
      MapLevels F body body' ->
      MapLevels F (TmForA id ty body) (TmForA id ty' body')
  | MapLvlAppl : forall g g' x x',
      MapLevels F g g' ->
      MapLevels F x x' ->
      MapLevels F (TmAppl g x) (TmAppl g' x')
  .
Theorem reflect_map_levels : forall f F t t',
  (forall x y, f x = y <-> F x y) ->
  map_levels f t = t' <-> MapLevels F t t'.
Proof.
  split; intros.
  - generalize dependent f. generalize dependent F. generalize dependent t'.
    induction t; intros; simpl in *; subst; constructor;
    try apply (IHt1 _ _ f); try apply (IHt2 _ _ f); try assumption; try reflexivity;
    apply H; reflexivity.
  - generalize dependent f. induction H0; intros; simpl in *;
    try (rewrite IHMapLevels1; [| assumption]); try (rewrite IHMapLevels2; [| assumption]);
    try reflexivity; f_equal; apply H0; assumption.
Qed.

(* Left fold. *)
Fixpoint fold_levels {T} (f : T -> nat -> T) (init : T) t :=
  match t with
  | TmVoid | TmVarS _ => init
  | TmStar lvl | TmAtom _ lvl => f init lvl
  | TmPack _ _ a b | TmForA _ a b | TmAppl a b => fold_levels f (fold_levels f init a) b
  end.
Inductive FoldLevels {T} (F : T -> nat -> T -> Prop) (init : T) : term -> T -> Prop :=
  | FoldLvlVoid :
      FoldLevels F init TmVoid init
  | FoldLvlVarS : forall id,
      FoldLevels F init (TmVarS id) init
  | FoldLvlStar : forall lvl lvl',
      F init lvl lvl' ->
      FoldLevels F init (TmStar lvl) lvl'
  | FoldLvlAtom : forall id lvl lvl',
      F init lvl lvl' ->
      FoldLevels F init (TmAtom id lvl) lvl'
  | FoldLvlPack : forall id arg ty curry tmp out,
      FoldLevels F init ty tmp ->
      FoldLevels F tmp curry out ->
      FoldLevels F init (TmPack id arg ty curry) out
  | FoldLvlForA : forall arg ty body tmp out,
      FoldLevels F init ty tmp ->
      FoldLevels F tmp body out ->
      FoldLevels F init (TmForA arg ty body) out
  | FoldLvlAppl : forall f x tmp out,
      FoldLevels F init f tmp ->
      FoldLevels F tmp x out ->
      FoldLevels F init (TmAppl f x) out
  .
Theorem reflect_fold_levels : forall {T} f F (init : T) t t',
  (forall a b c, f a b = c <-> F a b c) ->
  fold_levels f init t = t' <-> FoldLevels F init t t'.
Proof.
  split; intros.
  - generalize dependent T. induction t; intros; simpl in *; subst;
    econstructor; try eapply IHt1; try eapply IHt2; try apply H; reflexivity.
  - generalize dependent f. induction H0; intros; simpl in *; subst;
    try apply H0; try rewrite IHFoldLevels1; try apply IHFoldLevels2; try assumption; reflexivity.
Qed.

Definition Successor : nat -> nat -> Prop := fun m n => n = S m.
Arguments Successor m n/.
Definition Raise : term -> term -> Prop := MapLevels Successor.
Arguments Raise/ t t'.
Definition raise : term -> term := map_levels S.
Arguments raise/ t.
Theorem reflect_raise : forall t t',
  raise t = t' <-> Raise t t'.
Proof. intros. apply reflect_map_levels. unfold Successor. split; intros; symmetry in H; assumption. Qed.

Definition Max : nat -> nat -> nat -> Prop := fun a b c => Nat.max a b = c.
Arguments Max/ a b c.
Definition HighestLevel : term -> nat -> Prop := FoldLevels Max O.
Arguments HighestLevel/ t lvl.
Definition highest_level : term -> nat := fold_levels Nat.max O.
Arguments highest_level/ t.
Theorem reflect_highest_level : forall t lvl,
  highest_level t = lvl <-> HighestLevel t lvl.
Proof. intros. apply reflect_fold_levels. unfold Max. reflexivity. Qed.
