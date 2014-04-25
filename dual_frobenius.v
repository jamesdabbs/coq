Definition lem := forall p, p \/ ~p.

Definition frobenius := forall (A : Set) (p : A -> Prop) (q: Prop),
  (forall x : A, q \/ p x) <-> (q \/ forall x : A, p x).

Theorem lem_to_frobenius : lem -> frobenius.
Proof.
  unfold lem, frobenius.
  firstorder.
  destruct (H q); firstorder.
Qed.

Theorem frobenius_to_lem : frobenius -> lem.
Proof.
  unfold lem, frobenius.
  firstorder.
  destruct (H {_ : unit | p} (fun _ => False) p) as [G _].
  cut (p \/ ({_ : unit | p} -> False)).
  intros [K1 | K2]; firstorder.
  apply G.
  firstorder.
Qed.
