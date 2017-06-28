Require Import Arith Omega.
Import Nat.

Fixpoint multy (m n: nat): nat :=
  match m with
    | O => O
    | S p => multy p n + n
  end.

(* Possibly useful lemma from the standard library. *)
Check mul_comm: forall m n, m * n = n * m.

Lemma equiv:
  forall m n, multy m n = m * n.
Proof.
  induction m; simpl; intros; auto.
  rewrite IHm; omega.
Qed.

Lemma multy_m_Sn:
  forall m n, m + multy m n = multy m (S n).
Proof.
  intros; repeat (rewrite equiv).
  rewrite (mul_comm _ (S n)).
  simpl.
  rewrite (mul_comm n).
  omega.
Qed.
