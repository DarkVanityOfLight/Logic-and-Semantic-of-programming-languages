Require Import Lia.
Require Import PeanoNat.
(* Shee 0 *)

(* Let's start with some definitions *)

(* Let's define what a formula is *)
Inductive Formula : Type :=
    | Atomic : nat -> Formula (* Represents a variable denoted by a int *)
    | Unary : Formula -> Formula (* Represents a unary operator like Not *)
    | Binary : Formula -> Formula -> Formula (* Represents a binary operator like And *)
.

(* v(A) *)
(* Given a formula A, return the number of variable occurences *)
Fixpoint v (A : Formula) : nat :=
    match A with
    | Atomic _ => 1
    | Unary phi => v(phi)
    | Binary phi1 phi2 => v(phi1) + v(phi2)
    end.

(* k(A) *)
(* 
    Given a formula A, return the number of parenthese pairs,
    Note:
    A valid formula has to have parentheses around every operator so:
    (NOT a) is a valid formula while
    NOT A is not.
*)

Fixpoint k(A : Formula) : nat :=
    match A with
    | Atomic _ => 0
    | Unary phi => 1 + k(phi)
    | Binary phi1 phi2 => 1 + k(phi1) + k(phi2)
    end.

(* op(A) *)
(* Given a formula A, return the number of operators in the formula *)
Fixpoint op (A : Formula) : nat :=
    match A with
    | Atomic _ => 0
    | Unary phi => 1 + op(phi)
    | Binary phi1 phi2 => 1 + op(phi1) + op(phi2)
    end.

(* bop(A) *)
(* Given a formula A, return the number of binary operators in the formula*)
Fixpoint bop (A : Formula) : nat :=
    match A with
    | Atomic _ => 0
    | Unary phi => bop(phi)
    | Binary phi1 phi2 => 1 + bop(phi1) + bop(phi2)
    end.

(* Exercise 5 *)

(* 
    Let F be the set of all propositional formulas.
    Prove the following statements by using structural induction over the structure of propositional formulas:
    Every propositional formula A in F contains the same number of parentheses-pairs and operators:
    > For all A in F : k(A) =  op(A)
*)

(* Let's define the base case with a formula consisting of one variable*)
Lemma atomic_k_eq_op : forall(n : nat),
  k(Atomic n) = op(Atomic n).
Proof.
intros A. simpl. trivial.
Qed.

(* Now we proof it for unary operators *)
Lemma unary_k_eq_op : forall(A : Formula),
  k(A) = op(A) ->
  k(Unary A) = op(Unary A).
Proof.
  intros. simpl. apply f_equal. apply H.
Qed.

(* And at last for binarys *)
Lemma binary_k_eq_op : forall(A B : Formula),
  k(A) = op(A) ->
  k(B) = op(B) ->
  k(Binary A B) = op(Binary A B).
Proof.
  intros. simpl. 
  apply f_equal.
  rewrite H. rewrite H0.
  trivial.
Qed.

(*Now we can prove our theorem via induction*)
Theorem k_eq_op : forall(A : Formula),
  k(A) = op(A).
Proof.
  intros. induction A.
  - apply atomic_k_eq_op.
  - apply unary_k_eq_op. apply IHA.
  - apply binary_k_eq_op; apply IHA1 + apply IHA2.
Qed.

(* Exercise 6 *)

(* 1. *)
(*
  Let n be the number of variable occurences in A in F. 
  Then the number of operators in A is at least n-2:
  > For all A in F : op(A) >= v(A) - 2
*)

Lemma atomic_op_eq_v_mt : forall(n : nat),
  op(Atomic n) >= v(Atomic n) - 1.
Proof.
  intros. simpl. unfold ge. apply le_n.
Qed.

(* Instead of proofing for -2 we proof the stronger -1 *)
Lemma unary_op_eq_v_mt : forall(A : Formula),
  op(A) >= v(A) - 1 ->
  op(Unary A) >= v(Unary A) - 1.
Proof.
  intros. simpl. apply le_S. apply H.
Qed.

Lemma binary_op_eq_v_mt : forall(A B: Formula),
  op(A) >= v(A) - 1 ->
  op(B) >= v(B) - 1 ->
  op(Binary A B) >= v(Binary A B) - 1.
Proof.
  intros. simpl. lia.
Qed.
  
(* Helping lemma to get from the stronger to the weaker*)
Lemma smplge : forall(n1 n2 : nat),
  n1 >= n2 ->
  n1 >= pred n2.
Proof.
  intros. lia.
Qed.



(* Proofing the stronger theorem op(A) >= v(A) - 1*)
Theorem op_eq_v_mts : forall(A : Formula),
  op(A) >= v(A) - 1.
Proof.
  intros. induction A.
  - apply atomic_op_eq_v_mt.
  - apply unary_op_eq_v_mt. apply IHA.
  - apply binary_op_eq_v_mt; apply IHA1 + apply IHA2.
Qed.

(* Proof of the actuall theorem using the helper smplgemo *)
Lemma smplgemo : forall(n1 n2 : nat),
  n1 >= n2 - 1 ->
  n1 >= n2 - 2.
Proof.
  intros. simpl. lia.
Qed.

Theorem op_eq_v_mt : forall(A : Formula),
  op(A) >= v(A) -2.
Proof.
  intros. apply smplgemo. apply op_eq_v_mts.
Qed.
