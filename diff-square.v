Require Import Omega Arith.
Import Nat.

Definition sq n := n * n.

(* Some useful lemmas from the standard library. *)
Check mul_sub_distr_l: forall n m p, p * (n - m) = p * n - p * m.
Check mul_add_distr_r: forall n m p, (n + m) * p = n * p + m * p.
Check mul_comm: forall n m, n * m = m * n.

Lemma difference_of_squares:
  forall a b, sq a - sq b = (a + b) * (a - b).
Proof.

Qed.
