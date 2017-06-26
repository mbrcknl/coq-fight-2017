Inductive nat: Set :=
  | O: nat
  | S: nat -> nat.

Fixpoint plus (m n: nat): nat :=
  match m with
    | O => n
    | S p => S (plus p n)
  end.

Infix "+" := plus.

Lemma plus_comm:
  forall m n, m + n = n + m.
Proof.

Qed.
