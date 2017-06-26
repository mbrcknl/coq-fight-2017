Require Import Arith.
Import Nat.

Fixpoint evenb (n: nat): bool :=
  match n with
    | O => true
    | S p => negb (evenb p)
  end.

(* Some useful lemmas from the standard library. *)
Check even_succ: forall n, even (S n) = odd n.
Check negb_even: forall n, negb (even n) = odd n.

Lemma evenb_even:
  forall n, evenb n = even n.
Proof.

Qed.
