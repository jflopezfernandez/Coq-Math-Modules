
Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.

Fixpoint plus (a b : nat) : nat :=
  match a with
    | O => b
    | S a' => S (plus a' b)
  end.

Lemma AdditiveIdentity (a : nat) : plus a O = a.
Proof.
  induction a.
  - reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Lemma AdditiveSuccessor (a b : nat) : plus a (S b) = S (plus a b).
Proof.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Lemma AdditiveCommutativity (a b : nat) : plus a b = plus b a.
Proof.
  induction a.
  - simpl. rewrite AdditiveIdentity. reflexivity.
  - simpl. rewrite IHa. rewrite AdditiveSuccessor. reflexivity.
Qed.
