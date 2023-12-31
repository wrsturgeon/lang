From Coq Require Import
  List
  String.

Definition ap_fst {A B C} : (A -> C) -> ((A * B) -> C) := fun f x => let (a, b) := x in f a.

Lemma existsb_map_fst : forall {A B} li f f' x y,
  (forall (a a' : A) (b b' : B), f (a, b) (a', b') = f' a a') ->
  existsb (f (x, y)) li = existsb (f' x) (map fst li).
Proof.
  induction li; intros; simpl in *. { reflexivity. }
  destruct a. simpl. rewrite H. destruct (f' x a). { reflexivity. } apply IHli. assumption.
Qed.

Definition fst_cmp {A B} := fun (a : string * A) (b : string * B) => eqb (fst a) (fst b).

Lemma has_cmp_fst : forall {T} li s t,
  existsb (@fst_cmp T T (s, t)) li = existsb (eqb s) (map fst li).
Proof.
  intros T li. induction li; intros; simpl in *. { reflexivity. }
  destruct a. unfold fst_cmp. simpl in *. destruct (eqb s s0). { reflexivity. }
  apply (IHli _ t).
Qed.
