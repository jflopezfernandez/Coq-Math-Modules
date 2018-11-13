
Goal forall A B C : Prop, A \/ B /\ C -> (A \/ B) /\ (A \/ C).
Proof.
  intros.
  split.
  - destruct H. left. assumption. right. destruct H. assumption.
  - destruct H. left. assumption. right. destruct H. assumption.
Qed.

Goal forall A B : Prop, (forall C : Prop, (A -> B -> C) -> C) -> A.
Proof.
  intros.
  apply H.
  intros.
  assumption.
Qed.

Goal forall A B : Prop, A -> B -> A.
Proof.
  intros.
  assumption.
Qed.

Goal forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Goal forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intro A.
  intro B.
  intro C.
  intro H.
  intro H1.
  intro H2.
  apply H.
  apply H2.
  apply H1.
  apply H2.
Qed.
