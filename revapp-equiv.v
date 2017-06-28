Require Import List.
Import ListNotations.

Fixpoint revapp (xs ys: list nat): list nat :=
  match xs with
    | [] => ys
    | x::r => revapp r (x::ys)
  end.

(* Some useful lemmas from the standard library. *)
Check app_assoc: forall t (xs ys zs: list t), xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Check app_nil_r: forall t (xs: list t), xs ++ [] = xs.

Lemma equiv:
  forall xs, revapp xs [] = rev xs.
Proof.
  assert (forall xs ys, revapp xs ys = rev xs ++ ys).
  induction xs; simpl; intros; auto.
  rewrite <- app_assoc.
  rewrite <- IHxs; simpl; auto.
  intros; specialize (H xs []).
  rewrite app_nil_r in H; auto.
Qed.
