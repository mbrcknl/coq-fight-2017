Require Import Omega.

Inductive le_evil: nat -> nat -> Prop :=
  | le_x: forall x, le_evil x x
  | le_pred: forall x y, le_evil (S x) y -> le_evil x y.

Lemma le_evil_equiv:
  forall x y, le_evil x y <-> x <= y.
Proof.

Qed.
