(* Sheet 0 *)

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
