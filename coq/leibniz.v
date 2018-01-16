Definition leibniz (A:Type) (x y:A) := forall P, P x -> P y.

Theorem from_leibniz : forall A x y, leibniz A x y -> x = y.
Proof.
  intros.
  unfold leibniz in X.
  pose proof (X (fun z => x = z)).
  simpl in H.
  now apply H.
Qed.

Theorem to_leibniz : forall A x y, x = y -> leibniz A x y.
Proof.
  intros.
  now subst.
Qed.

Theorem sym_leibniz : forall A:Type, forall (x y:A), leibniz A x y -> leibniz A y x.
Proof.
  unfold leibniz ; intros.
  pose proof (X (fun z => P z -> P x)).
  simpl in X1.
  now apply X1.
Qed.