Require Import List Arith.
Import Nat.

(* Possibly useful lemma from the standard library. *)
Check mul_comm: forall m n, m * n = n * m.

Lemma that's_evil:
  forall m n, fold_right plus 0 (repeat m n) = fold_right plus 0 (repeat n m).
Proof.
  assert (forall m n, fold_right plus 0 (repeat m n) = n * m).
  induction n; simpl; auto.
  intros; repeat (rewrite H).
  apply mul_comm.
Qed.
