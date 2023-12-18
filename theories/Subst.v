From Coq Require Import
  Lists.List.
Import ListNotations.
From Lang Require Import
  Closed
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

Theorem map_fst_smap : forall f li,
  map fst (smap f li) = map fst li.
Proof. induction li. { reflexivity. } destruct a. simpl. rewrite IHli. reflexivity. Qed.

(* Ludicrous that this is the easiest correct definition to write.
 * Generates substitution functions for every free variable at once. *)
Fixpoint grand_unified_subst t : list (string * (term -> term)) :=
  match t with
  | TmVoid
  | TmStar
  | TmAtom _ =>
      []
  | TmVarS s =>
      [(s, fun x => x)]
  | TmPack id None a b =>
      smap (fun f x => TmPack id None (f x) b) (grand_unified_subst a) ++
      smap (fun f x => TmPack id None a (f x)) (grand_unified_subst b)
  | TmForA None a b =>
      smap (fun f x => TmForA None (f x) b) (grand_unified_subst a) ++
      smap (fun f x => TmForA None a (f x)) (grand_unified_subst b)
  | TmAppl a b =>
      smap (fun f x => TmAppl (f x) b) (grand_unified_subst a) ++
      smap (fun f x => TmAppl a (f x)) (grand_unified_subst b)
  | TmPack id (Some arg) ty curry =>
      smap (fun f x => TmPack id (Some arg) (f x) curry) (grand_unified_subst ty) ++
      smap (fun f x => TmPack id (Some arg) ty (f x))
      match grand_unified_subst curry with
      | [] => []
      | (s, hd) :: tl => if eqb arg s then tl else (s, hd) :: tl
      end
  | TmForA (Some arg) ty curry =>
      smap (fun f x => TmForA (Some arg) (f x) curry) (grand_unified_subst ty) ++
      smap (fun f x => TmForA (Some arg) ty (f x))
      match grand_unified_subst curry with
      | [] => []
      | (s, hd) :: tl => if eqb arg s then tl else (s, hd) :: tl
      end
  end.

Fixpoint pair_lookup {V} key (pairs : list (string * V)) :=
  match pairs with
  | [] => None
  | (k, v) :: tl => if eqb key k then Some v else pair_lookup key tl
  end.

Definition subst x y t := option_map (fun f => f y) (pair_lookup x (grand_unified_subst t)).
Arguments subst x y t/.

Example subst_simple : forall f x,
  subst f TmStar (TmAppl (TmVarS f) x) = Some (TmAppl TmStar x).
Proof. intros. simpl. rewrite eqb_refl. reflexivity. Qed.

Example grand_unified_subst_simple :
  grand_unified_subst (TmAppl (TmVarS "f"%string) (TmVarS "x"%string)) = [
    ("f"%string, fun t => TmAppl t (TmVarS "x"%string));
    ("x"%string, fun t => TmAppl (TmVarS "f"%string) t)].
Proof. reflexivity. Qed.

Theorem grand_unified_subst_exactly_fv : forall t,
  fv t = map fst (grand_unified_subst t).
Proof.
  intros t. induction t; intros; simpl in *; try reflexivity;
  repeat rewrite IHt1; repeat rewrite IHt2; try destruct arg;
  repeat rewrite map_distr; repeat rewrite map_fst_smap; f_equal;
  destruct (grand_unified_subst t2); simpl in *; try reflexivity;
  destruct p; simpl in *; destruct (eqb s s0); reflexivity.
Qed.
(* WOOHOOOOOOOOOOOOOOO *)

(* TODO: Inductive equivalent *)
