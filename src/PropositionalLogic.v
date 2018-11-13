
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

Lemma ImplicationsAreTransitive : (forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R).
Proof.
  intro P.
  intro Q.
  intro R.

  intro H1.
  intro H2.

  intro p.

  apply H2.
  apply H1.

  assumption.
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

Theorem Contrapositive : (forall P Q : Prop, (P -> Q) -> ~Q -> ~P).
Proof.
  intro P.
  intro Q.
  intro H.
  unfold not.
  apply ImplicationsAreTransitive.
  assumption.
Qed.

Theorem Conjunction : (forall P Q : Prop, P -> Q -> P /\ Q).
Proof.
  intro P.
  intro Q.
  intro p.
  intro q.
  split.
  - assumption.
  - assumption.
Qed.

Theorem Disjunction : (forall P Q : Prop, P -> P \/ Q).
Proof.
  intro P.
  intro Q.
  intro p.
  left.
  - assumption.
Qed.

Theorem AndIsCommutative : (forall P Q : Prop, P /\ Q -> Q /\ P).
Proof.
  intro P.
  intro Q.
  intro R.
  elim R.
  intro p.
  intro q.
  split.
  - assumption.
  - assumption.
Qed.

Theorem OrIsCommutative : (forall P Q : Prop, P \/ Q -> Q \/ P).
Proof.
  intro P.
  intro Q.
  intro R.
  elim R.
  - intro p. right. assumption.
  - intro q. left. assumption.
Qed.

Theorem ImplicationEquivalency : (forall P Q : Prop, (P -> Q) -> P -> (~P \/ Q)).
Proof.
  intro P.
  intro Q.
  intro H.
  intro p.
  right.
  apply H.
  assumption.
Qed.

Theorem ImplicationEquivalenceNotP : (forall P Q : Prop, (P -> Q) -> ~P -> (~P \/ Q)).
Proof.
  intro P.
  intro Q.
  intro H.
  intro notP.
  left.
  assumption.
Qed.

Theorem ModusTollens : (forall P Q : Prop, (P -> Q) -> ~Q -> ~P).
Proof.
  intro P.
  intro Q.
  intro H.

  unfold not.

  apply (ImplicationsAreTransitive).

  assumption.
Qed.





