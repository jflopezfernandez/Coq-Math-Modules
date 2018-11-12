
Require Import Unicode.Utf8.

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
