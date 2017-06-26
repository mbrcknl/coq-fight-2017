Require Import Omega.

Inductive less_eq: nat -> nat -> Prop :=
  | less_eq_O: forall y, less_eq 0 y
  | less_eq_S: forall x y, less_eq x y -> less_eq (S x) (S y).

Hint Constructors less_eq.

Lemma le_less_eq_equiv:
  forall x y, less_eq x y <-> x <= y.
Proof.

Qed.
