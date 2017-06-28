Fixpoint abacus (m n: nat): nat :=
  match m with
    | O => n
    | S p => abacus p (S n)
  end.

Lemma abacus_plus:
  forall m n, abacus m n = m + n.
Proof.
  induction m; simpl; intros; auto.
  rewrite <- IHm; clear IHm.
  revert n; induction m; simpl; auto.
Qed.
