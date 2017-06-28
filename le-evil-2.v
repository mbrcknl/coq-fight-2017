Require Import Omega.

Inductive le_evil: nat -> nat -> Prop :=
  | le_x: forall x, le_evil x x
  | le_pred: forall x y, le_evil (S x) y -> le_evil x y.

Hint Resolve le_x.

Lemma exorcise:
  forall x y, le_evil x y -> le_evil x (S y).
Proof.
  induction 1; constructor; auto.
Qed.

Hint Resolve exorcise.

Lemma le_evil_equiv:
  forall x y, le_evil x y <-> x <= y.
Proof.
  split; induction 1; auto; omega.
Qed.
