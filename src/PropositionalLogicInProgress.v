
Section MinimalPropositionalLogic.

Axiom P : Prop.
Axiom Q : Prop.
Axiom R : Prop.
Axiom T : Prop.

Theorem ImplicationsAreTransitive : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intro H0.
  intro H1.
  intro p.
  apply H1.
  apply H0.
  assumption.
Qed.

Section AssumptionExample.

Hypothesis H : P -> Q -> R.

Lemma L1 : P -> Q -> R.
Proof.
  assumption.
Qed.

End AssumptionExample.

Theorem ApplyExample : (Q -> R -> T) -> (P -> Q) -> P -> R -> T.
Proof.
  intros H1 H2 p.
  apply H1.
  exact (H2 p).
Qed.

(*
Theorem ImplicationIsDistributive : (forall A B C : Prop, (A -> (A -> B -> C) -> (A -> B) -> (B -> C))).
Proof.
  intro A.
  intro B.
  intro C.
  intro a.
  intro H1.
  intro H2.
  intro H3.
  apply H1.
  assumption.
  apply H3.
Qed.

*)


Theorem ImplicationIsDistributive : ((P -> Q -> R) -> (P -> Q) -> (P -> R)).
Proof.
  intros H1 H2 p.
  apply H1.
  assumption.
  exact (H2 p).
Qed.

Section ExamplesCh3Section3.

Lemma Identity : (P -> P).
Proof.
  intro p.
  exact p.
Qed.

Lemma IdentityImplication : ((P -> P) -> (P -> P)).
Proof.
  intro H0.
  exact H0.
Qed.

Lemma ImplicationIsTransitive : ((P -> Q) -> (Q -> R) -> P -> R).
Proof.
  intro H1.
  intro H2.
  intro p.
  apply H2.
  exact (H1 p).
Qed.

Lemma ImplicationPer : ((P -> Q -> R) -> (Q -> P -> R)).
Proof.
  intro H1.
  intro H2.
  intro p.
  apply H1.
  - assumption.
  - apply H2.
Qed.

Lemma IgnoreQ : ((P -> R) -> P -> Q -> R).
Proof.
  intro H1.
  intro H2.
  intro H3.
  apply H1.
  apply H2.
Qed.

Lemma DeltaImplication : ((P -> Q) -> (P -> P -> Q)).
Proof.
  intro H1.
  intro H2.
  intro H3.
  apply H1.
  apply H2.
Qed.

Lemma DeltaImplicationReverse : ((P -> P -> Q) -> P -> Q).
Proof.
  intro H1.
  intro H2.
  apply H1.
  assumption.
  assumption.
Qed.

Lemma Diamond : ((P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T).
Proof.
  intro H1.
  intro H2.
  intro H3.
  intro H4.
  apply H3.
  apply H1.
  apply H4.
  apply H2.
  assumption.
Qed.

Lemma WeakPeirce : (((((P -> Q) -> P) -> P) -> Q) -> Q).
Proof.
  intro H1.
  apply H1.
  intro H2.
  apply H2.
  intro H3.
  apply H1.
  intro H4.
  assumption.
Qed.

End ExamplesCh3Section3.

Theorem ModusPonens : ((P -> Q) -> P -> Q).
Proof.
  intros.
  rename H into H1.
  apply H1.
  assumption.
Qed.

(* TODO: Complete
Theorem ModusTollens : ((P -> Q) -> ~Q -> ~P).
Proof.
  intros.
*)

Section ProofOfTripleImplication.

Hypothesis H : (((P -> Q) -> Q) -> Q).
Hypothesis p : P.

Lemma Rem : ((P -> Q) -> Q).
Proof (fun H0: (P -> Q) => H0 p).

Theorem TripleImplication : Q.
Proof (H Rem).

End ProofOfTripleImplication.

Print TripleImplication.

Print Rem.

Theorem ThenExample : (P -> Q -> (P -> Q -> R) -> R).
Proof.
  intros p q H1.
  apply H1; assumption.
Qed.

Theorem TripleImplicationOneShot : ((((P -> Q) -> Q) -> Q) -> P -> Q).
Proof.
  intros H p; apply H; intro H0; apply H0; assumption.
Qed.

Theorem ComposeExample : ((P -> Q -> R) -> (P -> Q) -> (P -> R)).
Proof.
  intros H1 H2 p.
  apply H1; [assumption | apply H2; assumption].
Qed.

Lemma L3 : ((P -> Q) -> (P -> R) -> (P -> Q -> R -> T) -> P -> T).
Proof.
  intros H1 H2 H3 p.
  apply H3; [idtac | apply H1 | apply H2]; assumption.
Qed.

Theorem ThenFailExample : ((P -> Q) -> (P -> Q)).
Proof.
  intro H; apply H; fail.
Qed.

Section SectionForCutExample.

Hypothesis (H1 : P -> Q)
           (H2 : Q -> R)
           (H3 : (P -> R) -> T -> Q)
           (H4 : (P -> R) -> T).

Theorem CutExample : Q.
Proof.
  cut (P -> R).
  intro H5.
  apply H3.
  assumption.
  apply H4; assumption.
  intro H6.
  apply H2.
  apply H1.
  assumption.
Qed.

Print CutExample.

Theorem CutWithoutCutExample : Q.
Proof.
  apply H3.
  intro H5.
  apply H2.
  apply H1.
  assumption.
  apply H4.
  intro H5.
  apply H2.
  apply H1.
  assumption.
Qed.

End SectionForCutExample.

End MinimalPropositionalLogic.

Print ImplicationIsDistributive.

Section UsingImplicationIsDistributive.

Variables (P1 P2 P3 : Prop).

(* Not working

Check (ImplicationIsDistributive P1 P2 P3).

*)

Theorem Exercise5P5 : (forall A B C D : Set, A = C \/ B = C \/ C = C \/ D = C).
Proof.
  intro A.
  intro B.
  intro C.
  intro D.
  right.
  right.
  left.
  reflexivity.
Qed.


Theorem ModusTollens : (forall P Q : Prop, (P -> Q) -> ~Q -> ~P).
Proof.
  intro P.
  intro Q.
  intro H.
  unfold not.
  apply (ImplicationTransitivity).
  exact (H).
Qed.
