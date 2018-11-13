
Require Import Unicode.Utf8.

Theorem ModusPonens : (forall P Q : Prop, P -> (P -> Q) -> Q).
Proof.
  intro P.
  intro Q.
  intro p.
  intro H.
  exact (H p).
Qed.

Theorem DoubleNegation : (forall P : Prop, P -> ~~P).
Proof.
  intro P.
  intro p.
  unfold not.
  intro notP.
  exact (notP p).
Qed.

Theorem ImplicationTransitivity : (forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R).
Proof.
  intro P.
  intro Q.
  intro R.
  intro H1.
  intro H2.
  intro p.
  apply H2.
  exact (H1 p).
Qed.

Theorem Absurd : (forall P Q : Prop, P -> ~P -> Q).
Proof.
  intro P.
  intro Q.
  intro p.
  intro H.
  elim H.
  assumption.
Qed.

Theorem Contrapositive : (forall A B : Prop, (A -> B) -> ~B -> ~A).
Proof.
  intro A.
  intro B.
  intro H1.
  unfold not.
  apply ImplicationTransitivity.
  apply H1.
Qed.
