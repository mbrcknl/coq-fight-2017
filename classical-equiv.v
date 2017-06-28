Lemma classical_equiv:
  (forall P, (~P -> P) -> P) -> forall P, P \/ ~ P.
Proof.
  intros H P.
  apply H; intros J.
  right.
  intros N.
  apply J.
  left.
  assumption.
Qed.
