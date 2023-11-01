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
