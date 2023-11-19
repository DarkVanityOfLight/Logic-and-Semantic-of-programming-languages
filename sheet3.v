Require Import Classical.

Lemma trivial_implication : forall(A : Prop),
  A ->
  A.
Proof.
  intros. apply H.
Qed.

Lemma remove_double_negation : forall(A : Prop),
  ~~A ->
  A.
Proof.
  intros. apply NNPP in H. apply H.
Qed.

Lemma contraposition : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof.
  intros A B H1 H2.
  intro Ha.
  apply H2.
  apply H1.
  apply Ha.
Qed.

Lemma implication_from_inconsistency : forall A B : Prop, ~B -> (B->A).
Proof.
  intros.
  contradiction.
Qed.  
 
Lemma elimination_of_assumptions : forall A B : Prop,
  (B -> A) -> ((~B -> A) -> A).
Proof.
  intros A B H1 H2.
  destruct (classic B) as [H3 | H3].
  - apply H1. assumption.
  - apply H2. assumption.
Qed.


Theorem a : forall(x y : Prop),
  x -> ((x -> y) -> y).
Proof.
  intros x y H1 H2.
  apply H2.
  apply H1.
Qed.

Theorem b : forall(p q : Prop),
  ~p -> (p -> (p -> q)).
Proof.
  intros. apply implication_from_inconsistency with (B := p).
  - apply H.
  - apply H1.
Qed.
  
  
