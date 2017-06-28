Require Import Arith Omega.

Fixpoint fast (a b n: nat): nat :=
  match n with
    | O => a
    | S p => fast b (a+b) p
  end.

Fixpoint slow (a b n: nat): nat :=
  match n with
    | O => a
    | 1 => b
    | S (S pp as p) => slow a b pp + slow a b p
  end.

Lemma equiv:
  forall n a b, slow a b n = fast a b n.
Proof.
  induction n using lt_wf_ind; intros.
  destruct n; simpl; auto.
  rewrite (H n); try omega.
  destruct n; simpl; auto.
  rewrite (H n); try omega.
  clear H; revert a b.
  induction n; simpl; auto.
Qed.
