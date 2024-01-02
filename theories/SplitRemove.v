From Coq Require Export
  List.
Export ListNotations.
From Lang Require Import
  NonEmpty.

Fixpoint splitrm_once_slow {T} (f : T -> bool) li :=
  match li with
  | [] => None
  | hd :: tl =>
      if f hd then Some ([], tl) else
      option_map (fun p : _ * _ => let (a, b) := p in (hd :: a, b)) (splitrm_once_slow f tl)
  end.
Fixpoint splitrm_once_fast {T} acc (f : T -> bool) li :=
  match li with
  | [] => None
  | hd :: tl => if f hd then Some (rev acc, tl) else splitrm_once_fast (hd :: acc) f tl
  end.
Definition splitrm_once {T} := @splitrm_once_fast T [].
Arguments splitrm_once {T}/ f li.

Lemma splitrm_once_fast_acc : forall {T} hd tl f li,
  splitrm_once_fast (hd ++ tl) f li =
  option_map (fun p : _ * _ => let (a, b) := p in (rev tl ++ a, b)) (@splitrm_once_fast T hd f li).
Proof.
  intros. generalize dependent hd. generalize dependent tl. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. } destruct (f a). { simpl. rewrite rev_app_distr. reflexivity. }
  apply (IHli _ _ (a :: hd)).
Qed.

Theorem splitrm_once_fast_slow : forall {T} f li,
  splitrm_once f li = @splitrm_once_slow T f li.
Proof.
  intros. generalize dependent f. induction li; intros; simpl in *. { reflexivity. }
  destruct (f a). { reflexivity. } rewrite (splitrm_once_fast_acc [] [a]). f_equal. apply IHli.
Qed.

Theorem splitrm_once_app : forall {T} f a b,
  splitrm_once f (a ++ b) =
  match @splitrm_once T f a with
  | None => option_map (fun p : _ * _ => let (pre, post) := p in (a ++ pre, post)) (splitrm_once f b)
  | Some (pre, post) => Some (pre, post ++ b)
  end.
Proof.
  intros T f a. generalize dependent f.
  induction a; intros; simpl in *. { destruct (splitrm_once_fast [] f b); [destruct p |]; reflexivity. }
  destruct (f a). { reflexivity. } repeat rewrite (splitrm_once_fast_acc [] [a]). rewrite IHa.
  destruct (splitrm_once_fast [] f a0); simpl. { destruct p. reflexivity. }
  destruct (splitrm_once_fast [] f b); [destruct p |]; reflexivity.
Qed.

Fixpoint splitrm_slow {T} (f : T -> bool) li :=
  match li with
  | [] => NESton []
  | hd :: tl => if f hd then NECons [] (splitrm_slow f tl) else ne_map_hd (cons hd) (splitrm_slow f tl)
  end.
Fixpoint splitrm_fast {T} acc (f : T -> bool) li :=
  match li with
  | [] => acc
  | hd :: tl => splitrm_fast (if f hd then NECons [] acc else ne_map_hd (cons hd) acc) f tl
  end.
Definition splitrm {T} f li := ne_revmap (@rev T) (@splitrm_fast T (NESton []) f li).
Arguments splitrm {T}/ f li.

Example splitrm_slow_12345 :
  exists y, ne [[1;2;3;4];[1;2;3;4];[1;2;3;4];[1;2]] = Some y /\
  splitrm_slow (Nat.eqb 5) [1;2;3;4;5;1;2;3;4;5;1;2;3;4;5;1;2] = y.
Proof. eexists. split. { reflexivity. } reflexivity. Qed.

Example splitrm_12345 :
  exists y, ne [[1;2;3;4];[1;2;3;4];[1;2;3;4];[1;2]] = Some y /\
  splitrm (Nat.eqb 5) [1;2;3;4;5;1;2;3;4;5;1;2;3;4;5;1;2] = y.
Proof. eexists. split. { reflexivity. } reflexivity. Qed.

Lemma splitrm_fast_acc : forall {T} hd tl f li,
  splitrm_fast (NECons hd tl) f li = ne_app (@splitrm_fast T (NESton hd) f li) tl.
Proof.
  intros. generalize dependent hd. generalize dependent tl. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. }
  destruct (f a). { repeat rewrite IHli. rewrite ne_app_assoc. reflexivity. }
  apply (IHli _ _ (a :: hd)).
Qed.

Lemma splitrm_fast_ston : forall {T} hd tl f li,
  splitrm_fast (NESton (hd ++ tl)) f li = ne_map_last (fun li => li ++ tl) (@splitrm_fast T (NESton hd) f li).
Proof.
  intros. generalize dependent hd. generalize dependent tl. generalize dependent f.
  induction li; intros; simpl in *. { reflexivity. }
  destruct (f a). { repeat rewrite splitrm_fast_acc. rewrite ne_map_last_app. reflexivity. }
  apply (IHli _ tl (a :: hd)).
Qed.

Lemma ne_rev_map_map_last : forall {T} a z,
  ne_rev (ne_map (@rev T) (ne_map_last (fun x => x ++ [a]) z)) = ne_map_hd (cons a) (ne_rev (ne_map (@rev T) z)).
Proof.
  intros. repeat rewrite ne_rev_fast_slow. generalize dependent a.
  induction z; intros; simpl in *. { rewrite rev_app_distr. reflexivity. }
  repeat rewrite ne_snoc_app. rewrite ne_map_hd_app. f_equal. apply IHz.
Qed.

Theorem splitrm_fast_slow : forall {T} f li,
  splitrm f li = @splitrm_slow T f li.
Proof.
  intros. simpl in *. rewrite ne_rev_map. generalize dependent f. induction li; intros; simpl in *. { reflexivity. }
  destruct (f a). { rewrite splitrm_fast_acc. rewrite ne_map_distr. rewrite ne_rev_distr. simpl. f_equal. apply IHli. }
  rewrite (splitrm_fast_ston [] [a]). rewrite ne_rev_map_map_last. f_equal. apply IHli.
Qed.

Lemma ne_map_hd_splitrm : forall {T} li a p,
  p a = false ->
  ne_map_hd (@cons T a) (splitrm_slow p li) = splitrm_slow p (a :: li).
Proof.
  induction li; intros; simpl in *. { rewrite H. reflexivity. } rewrite H. reflexivity.
Qed.
