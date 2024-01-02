From Coq Require Export
  List.
Export ListNotations.

Inductive non_empty T :=
  | NESton (hd : T)
  | NECons (hd : T) (tl : non_empty T)
  .
Arguments NESton {T} hd.
Arguments NECons {T} hd tl.

Definition ne_head {T} (li : non_empty T) := match li with NESton hd | NECons hd _ => hd end.

Fixpoint ne_snoc {T} x li :=
  match li with
  | NESton hd => @NECons T hd (NESton x)
  | NECons hd tl => NECons hd (ne_snoc x tl)
  end.
Example ne_snoc_12345 :
  ne_snoc 9 (NECons 1 (NECons 2 (NECons 3 (NECons 4 (NESton 5))))) =
  (NECons 1 (NECons 2 (NECons 3 (NECons 4 (NECons 5 (NESton 9)))))).
Proof. reflexivity. Qed.

Fixpoint ne_app {T} a b :=
  match a with
  | NESton hd => @NECons T hd b
  | NECons hd tl => NECons hd (ne_app tl b)
  end.

Theorem ne_snoc_app : forall {T} x li,
  ne_snoc x li = @ne_app T li (NESton x).
Proof. intros. generalize dependent x. induction li; intros; simpl in *. { reflexivity. } f_equal. apply IHli. Qed.

Theorem ne_app_assoc : forall {T} a b c,
  ne_app (ne_app a b) c = @ne_app T a (ne_app b c).
Proof. induction a; intros; simpl in *. { reflexivity. } f_equal. apply IHa. Qed.

Fixpoint ne_rev_slow {T} (li : non_empty T) :=
  match li with
  | NESton x => NESton x
  | NECons hd tl => ne_snoc hd (ne_rev_slow tl)
  end.
Fixpoint ne_rev_fast {T} acc (li : non_empty T) :=
  match li with
  | NESton hd => NECons hd acc
  | NECons hd tl => ne_rev_fast (NECons hd acc) tl
  end.
Definition ne_rev {T} li :=
  match li with
  | NESton hd => NESton hd
  | NECons hd tl => @ne_rev_fast T (NESton hd) tl
  end.
Arguments ne_rev {T} li.

Lemma ne_rev_acc : forall {T} hd tl li,
  ne_rev_fast (ne_app hd tl) li = @ne_app T (ne_rev_fast hd li) tl.
Proof.
  intros. generalize dependent hd. generalize dependent tl. induction li; intros; simpl in *. { reflexivity. }
  rewrite <- IHli. reflexivity.
Qed.

Lemma ne_rev_fast_ston : forall {T} acc li,
  ne_rev_fast (NESton acc) li = @ne_snoc T acc (ne_rev li).
Proof.
  intros. generalize dependent acc. induction li; intros; simpl in *. { reflexivity. }
  rewrite (ne_rev_acc (NESton hd) (NESton acc)). rewrite ne_snoc_app. reflexivity.
Qed.

Theorem ne_rev_fast_slow : forall {T} li,
  ne_rev li = @ne_rev_slow T li.
Proof. induction li; simpl in *. { reflexivity. } rewrite ne_rev_fast_ston. f_equal. assumption. Qed.

Theorem ne_rev_distr : forall {T} a b,
  ne_rev (ne_app a b) = @ne_app T (ne_rev b) (ne_rev a).
Proof.
  intros. repeat rewrite ne_rev_fast_slow. generalize dependent b. induction a; intros; simpl in *. { apply ne_snoc_app. }
  repeat rewrite ne_snoc_app. rewrite IHa. apply ne_app_assoc.
Qed.

Fixpoint ne_acc {T} acc (li : list T) :=
  match li with
  | [] => acc
  | hd :: tl => ne_acc (NECons hd acc) tl
  end.

Definition ne {T} (li : list T) :=
  match li with
  | [] => None
  | [x] => Some (NESton x)
  | hd :: tl => Some (ne_rev (ne_acc (NESton hd) tl))
  end.

Fixpoint ne_slow {T} (li : list T) :=
  match li with
  | [] => None
  | [x] => Some (NESton x)
  | hd :: tl => option_map (NECons hd) (ne_slow tl)
  end.

Theorem ne_acc_app : forall {T} hd tl li,
  ne_acc (ne_app hd tl) li = @ne_app T (ne_acc hd li) tl.
Proof.
  intros. generalize dependent hd. generalize dependent tl. induction li; intros; simpl in *. { reflexivity. }
  rewrite <- IHli. reflexivity.
Qed.

Theorem ne_acc_cons : forall {T} hd tl li,
  ne_acc (NECons hd tl) li = @ne_app T (ne_acc (NESton hd) li) tl.
Proof. intros. rewrite <- ne_acc_app. reflexivity. Qed.

Theorem ne_fast_slow : forall {T} li,
  ne li = @ne_slow T li.
Proof.
  induction li. { reflexivity. } destruct li. { reflexivity. } simpl in *. rewrite ne_acc_cons. rewrite ne_rev_distr.
  rewrite <- IHli. destruct li; reflexivity.
Qed.

Example ne_12345 : ne [1;2;3;4;5] = Some (NECons 1 (NECons 2 (NECons 3 (NECons 4 (NESton 5))))).
Proof. reflexivity. Qed.

Definition ne_map_hd {T} (f : T -> T) li :=
  match li with
  | NESton hd => NESton (f hd)
  | NECons hd tl => NECons (f hd) tl
  end.

Fixpoint ne_map {A B} (f : A -> B) li :=
  match li with
  | NESton hd => NESton (f hd)
  | NECons hd tl => NECons (f hd) (ne_map f tl)
  end.

Fixpoint ne_map_last {T} (f : T -> T) li :=
  match li with
  | NESton hd => NESton (f hd)
  | NECons hd tl => NECons hd (ne_map_last f tl)
  end.

Fixpoint ne_revmap_acc {A B} acc (f : A -> B) li :=
  match li with
  | NESton hd => NECons (f hd) acc
  | NECons hd tl => ne_revmap_acc (NECons (f hd) acc) f tl
  end.
Definition ne_revmap {A B} f li :=
  match li with
  | NESton hd => NESton (f hd)
  | NECons hd tl => @ne_revmap_acc A B (NESton (f hd)) f tl
  end.

Lemma ne_revmap_acc_cons : forall {A B} hd tl f li,
  ne_revmap_acc (NECons hd tl) f li = ne_app (@ne_revmap_acc A B (NESton hd) f li) tl.
Proof.
  intros. generalize dependent B. induction li; intros; simpl in *. { reflexivity. }
  repeat rewrite IHli. rewrite ne_app_assoc. reflexivity.
Qed.

Theorem ne_rev_map : forall {A B} f li,
  ne_revmap f li = ne_rev (@ne_map A B f li).
Proof.
  intros. rewrite ne_rev_fast_slow. generalize dependent B. induction li; intros; simpl in *. { reflexivity. }
  destruct li. { reflexivity. } simpl in *. rewrite ne_revmap_acc_cons. repeat rewrite ne_snoc_app.
  f_equal. rewrite <- ne_snoc_app. apply IHli.
Qed.

Theorem ne_map_distr : forall {A B} f a b,
  ne_map f (ne_app a b) = ne_app (@ne_map A B f a) (ne_map f b).
Proof. intros A B f a. generalize dependent B. induction a; intros; simpl in *. { reflexivity. } f_equal. apply IHa. Qed.

(* a nice consequence of non-emptiness *)
Theorem ne_map_hd_app : forall {T} f a b,
  ne_map_hd f (ne_app a b) = @ne_app T (ne_map_hd f a) b.
Proof. intros T f [] b; reflexivity. Qed.

Theorem ne_map_last_app : forall {T} f a b,
  ne_map_last f (ne_app a b) = @ne_app T a (ne_map_last f b).
Proof. intros T f a. generalize dependent f. induction a; intros; simpl in *. { reflexivity. } f_equal. apply IHa. Qed.

Fixpoint ne_fold {A B} (init : A -> B) (f : A -> B -> B) li :=
  match li with
  | NESton hd => init hd
  | NECons hd tl => f hd (ne_fold init f tl)
  end.

Fixpoint ne_intersp {T} (f : T -> T -> T) li :=
  match li with
  | NESton hd => hd
  | NECons hd tl => f hd (ne_intersp f tl)
  end.
