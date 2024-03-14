Require Export UniMath.Foundations.All.

Require Import l4_unimath_exercises.

(* Exercise 1 *)

(* Example 12.1.2 (second half) from Rijke: The empty type is a proposition. *)

Theorem Example12_1_2_2 : isaprop empty.
Proof.
  intros [].
Qed.

(* Exercise 2 *)

Theorem Ex2 {A : UU} : iscontr A → isaprop A.
Proof.
  intros [c h] x y.
  simpl.
  exists ((h x) @ !(h y)).
  intro t.
  induction t.
  induction (h x).
  apply idpath.
Qed.

(* Example 12.1.2 (first half) from Rijke: Every contractible type is a proposition. *)

(* Exercise 3 *)

Theorem Ex3 {A : UU} : A → isaprop A → iscontr A.
Proof.
  intros a h.
  exists a.
  intros t.
  induction (h t a) as [e _].
  exact e.
Qed.

(* (i ⇒ iii) in Proposition 12.1.3 of Rijke: If a proposition is inhabited, then it is contractible.*)

(* Exercise 4 *)

(* Proposition 12.4.3 of Rijke: If a type has h-level n, then it has h-level n+1.*)

Print isaprop.

Theorem Ex4 {A : UU} {n : nat}: isofhlevel n A → isofhlevel (S(n)) A.
  generalize A.
  induction n as [| p hp].
  - intros h.
    apply Ex2.
  - intros B h2.
    simpl in *.
    intros x y e1 e2.
    apply hp.
    apply h2.
Qed. 

(* Exercise 5 *)

(* Every statement of the form ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)
