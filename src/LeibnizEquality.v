
Require Import Unicode.Utf8.

Require Import Relations.

Section Leibniz.

  Set Implicit Arguments.
  Unset Strict Implicit.
  
  Variable A : Set.
  
  Definition Leibniz (a b : A) : Prop := (forall P : A -> Prop, P a -> P b).

  Theorem LeibnizSymmetric : (symmetric A Leibniz).
  Proof.
    unfold symmetric.
    
    intro x.
    intro y.
    intro H.
    intro Q.
    
    apply H.
    
    intro R.
    assumption.
  Qed.
  
  Theorem LeibnizReflexive : (reflexive A Leibniz).
  Proof.
    unfold reflexive.
    
    intro a.
    intro H.
    intro Q.
    
    assumption.
  Qed.
  
  Theorem LeibnizTransitive : (transitive A Leibniz).
  Proof.
    unfold transitive.
    
    intro x.
    intro y.
    intro z.
    
    intro Q.
    intro R.
    intro S.
    intro T.
    
    apply R.
    apply Q.
    
    assumption.
  Qed.
  
  Theorem LeibnizEquivalenceRelation : (equiv A Leibniz).
  Proof.
    unfold equiv.
    
    unfold reflexive.
    unfold transitive.
    unfold symmetric.
    
    split.
    - apply (LeibnizReflexive).
    - split.
    -- apply (LeibnizTransitive).
    -- apply (LeibnizSymmetric).
  Qed.
  
  