
(* Modus Ponens
 * 
 * P -> Q : If the lamp is broken, then the room is dark.
 * P      : The lamp is broken.
 * Q      : The room is dark.
 *
 *)

Section Definitions.

Definition Implication : (forall P Q : Prop, (P -> Q) -> P -> Q).
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Definition Contrapositive : (forall P Q : Prop, (P -> Q) -> P -> Q -> (~Q -> ~P)).
Proof.
  intros.
  intuition.
Qed.

Section Lemmas.

Lemma ModusPonens : (forall P Q : Prop, (P -> Q) -> P -> Q).
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Lemma ModusTollens : (forall P Q : Prop, (P -> Q) -> ~Q -> ~P).
Proof.
  intros.
  auto.
Qed.
