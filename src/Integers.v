
Require Import Unicode.Utf8.

Require Import ZArith.

Open Scope Z_scope.


Theorem IntegerMultiplicationIsDistributive : (forall a b : Z, a * b + b = (a + 1) * b).
Proof.
  intro a.
  intro b.
  
  rewrite Zmult_plus_distr_l.
  rewrite Zmult_1_l.
  
  reflexivity.
Qed.

Theorem IntegerRegroup5 : (forall a : Z, a + a + a + a + a = 5 * a).
Proof.
  intro a.
  pattern a at 1.
  
  rewrite <- Zmult_1_l.
  repeat rewrite IntegerMultiplicationIsDistributive.
  
  auto with zarith.
Qed.
