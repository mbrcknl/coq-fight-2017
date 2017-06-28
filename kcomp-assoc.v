Require Import List.
Import ListNotations.

Definition kcomp {A B C: Type} (f: B -> list C) (g: A -> list B): A -> list C :=
  fun x => concat (map f (g x)).

(* Use Search to find lemmas you need. For example: *)
Search app nil.

Lemma kcomp_assoc:
  forall A B C D (f: C -> list D) (g: B -> list C) (h: A -> list B) (v: A),
    kcomp f (kcomp g h) v = kcomp (kcomp f g) h v.
Proof.
  unfold kcomp; intros.
  remember (h v) as xs.
  clear v Heqxs.
  induction xs; simpl; auto.
  rewrite map_app.
  rewrite concat_app.
  rewrite IHxs.
  auto.
Qed.
