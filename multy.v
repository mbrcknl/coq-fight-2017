Require Import Arith Omega.
Import Nat.

Fixpoint multy (m n: nat): nat :=
  match m with
    | O => O
    | S p => multy p n + n
  end.

(* Possibly useful lemma from the standard library. *)
Check mul_comm: forall m n, m * n = n * m.

Lemma multy_m_Sn:
  forall m n, m + multy m n = multy m (S n).
Proof.

Qed.
