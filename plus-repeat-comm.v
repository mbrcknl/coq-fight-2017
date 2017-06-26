Require Import List Arith.
Import Nat.

(* Possibly useful lemma from the standard library. *)
Check mul_comm: forall m n, m * n = n * m.

Lemma that's_evil:
  forall m n, fold_right plus 0 (repeat m n) = fold_right plus 0 (repeat n m).
Proof.

Qed.
