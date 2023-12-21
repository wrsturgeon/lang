(* TODO: Change term to `Heavy` (for the opposite) *)

From Lang Require Import
  Terms.

(* Some types should be trivially copyable, but this should be tightly controlled.
 * For example, types themselves (whose types are `*`) should be usable as many times as we'd like,
 * but their specific instances shouldn't (unless they're also trivially copyable). *)
Inductive Mint : term -> Prop :=
  | MintVoid : (* why not *)
      Mint TmVoid
  | MintStar : forall univ, (* again, types, but not their instances *)
      Mint (TmStar univ) (* (e.g. \t:*. t -> t` is okay, but `\t: *. t -> (t * t)` will fail during typechecking *)
  | MintAtom : forall id,
      Mint (TmAtom id)
  | MintPack : forall id ty curry,
      Mint curry ->
      Mint (TmPack id None ty curry) (* NOT dependent: required not to take a named argument *)
  | MintForA : forall arg ty body, (* Just a function pointer, as long as it doesn't take a type. *)
      (~exists univ, ty = TmStar univ) -> (* TODO: Disallow capture in minted functions. *)
      Mint (TmForA arg ty body) (* ditto ^^^ *)
  .

Fixpoint mint (ty : term) : bool :=
  match ty with
  | TmVoid
  | TmStar _
  | TmAtom _ =>
      true
  | TmPack _ None _ curry =>
      mint curry
  | TmForA _ ty _ =>
      match ty with
      | TmStar _ => false
      | _ => true
      end
  | _ =>
      false
  end.

Theorem reflect_mint : forall ty,
  Bool.reflect (Mint ty) (mint ty).
Proof.
  induction ty; repeat constructor.
  - intro C. inversion C.
  - simpl. destruct arg.
    + constructor. intro C. inversion C.
    + destruct (mint ty2); inversion IHty2; constructor.
      * constructor. assumption.
      * intro C. inversion C. apply H. assumption.
  - simpl. destruct ty1; repeat constructor; try (intros [univ C]; discriminate).
    intro C. inversion C. apply H0. eexists. reflexivity.
  - intro C. inversion C.
Qed.

Theorem mint_true : forall ty,
  Mint ty <-> mint ty = true.
Proof. split; intros; destruct (reflect_mint ty). { reflexivity. } { contradiction. } { assumption. } { discriminate. } Qed.

Theorem mint_false : forall ty,
  (~Mint ty) <-> mint ty = false.
Proof. split; intros; destruct (reflect_mint ty). { contradiction. } { reflexivity. } { discriminate. } { assumption. } Qed.
