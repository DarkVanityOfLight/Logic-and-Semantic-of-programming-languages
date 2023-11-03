(* Sheet 1 *)

(* We need some definitions*)


(* A Formula *)
Inductive formula : Type :=
  | Var : nat -> formula (* Variable represented as a natural number *)
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Not : formula -> formula.

(* 
  A interpretation maps a variable to it's bool value. 
  We basically modell variables by numbering them.
*)
Definition interpretation := nat -> bool.

(*
  Given a Interpretation and a formula and a Interpretation
  we can evaluate the formula to either true or false.
*)
Fixpoint eval (phi : formula) (I : interpretation) : bool :=
  match phi with
  | Var v => I v
  | And phi1 phi2 => (eval phi1 I) && (eval phi2 I)
  | Or phi1 phi2 => (eval phi1 I) || (eval phi2 I)
  | Not phi => negb (eval phi I)
  end.

(*Aufgabe 7*)
(* 
  Given a Formula phi and two Interpretations:
  I_1, I_2 : V -> {1, 0}
  Where V is the set of all Variables. For which the Value of every in phi existing Variable is the same, then 
  I_1(phi) = I_2(phi)
*)
Theorem interpretation_agreement :
  forall (phi : formula) (I1 I2 : interpretation),
  (forall v, I1 v = I2 v) ->
  eval phi I1 = eval phi I2.
Proof.
  intros.
  induction phi.
  - apply H.
  - simpl. rewrite IHphi1. rewrite IHphi2. reflexivity.
  - simpl. rewrite IHphi1. rewrite IHphi2. reflexivity.
  - simpl. rewrite IHphi. reflexivity.
Qed.
