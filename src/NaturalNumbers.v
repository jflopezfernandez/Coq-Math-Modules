
Require Import Unicode.Utf8.

Open Scope nat_scope.

Theorem NAdditionAssociative : (forall x y z : nat, (x + y) + z = x + (y + z)).
Proof.
  intro x.
  intro y.
  intro z.
  
  induction x.
  
  rewrite plus_O_n.
  rewrite plus_O_n.
  
  reflexivity.
  
  rewrite (plus_Sn_m x y).
  rewrite (plus_Sn_m (x + y) z).
  rewrite (plus_Sn_m).
  rewrite IHx.
  
  reflexivity.
Qed.
