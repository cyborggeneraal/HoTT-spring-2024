Require Export UniMath.Foundations.All.

(* Exercise 1*)

(*bool is defined as the following in UniMath.Foundations.Preamble:

Inductive bool : UU :=
  | true : bool
  | false : bool.

*)

Definition not : bool → bool.
Proof.
  intro b.
  induction b.
  - exact false.
  - exact true.
Defined.

Compute (not true).
Compute (not false).

Print not.
(*
 Notes:
 - bool_rect is what we call ind_bool in the lecture.
 - The argument (λ _ : bool, bool) : bool -> Type is implicit in the lecture.*)

(* Exercise 2 *)

Search (UU → UU → UU).
About coprod.

Definition distr {A B C : UU} : (A × B) ⨿ (A × C) → A × (B ⨿ C).
(* ⨿ is ~\amalg~ *)
Proof.
  intro.
  induction X.
  - induction a as [a b].
    split.
    + exact a.
    + exact (inl b).
  - induction b as [a c].
    split.
    + exact a.
    + exact (inr c).
Defined.

(* Exercise 3 *)

(* Write ∑ as ~\Sigma~ and terms as (a,,b).*)

Definition π1 {P : UU} (Q : P → UU) : (∑ (x : P), Q x) → P.
Proof.
  intro s.
  induction s as [p q].
  exact p.
Defined.

(*Exercise 4*)

Definition add : nat → nat → nat.
Proof. 
    intro n.
    intro m.
    induction m.
    - exact n.
    - exact (S IHm).
Defined.

Compute (add 5 7).
Compute (add 12 21).

Print add.


(*-------------------*)

(* Exercise 5 *)

Definition boolRep : bool → UU.
(* Send false to empty, the type with no constructors and true to unit, the type with one constructor. *)
Proof.
  intros [|]; [exact unit | exact empty].
Defined.

(* Exercise 6 *)

Definition ι : bool → nat.
Proof.
  intros [|]; [exact 1 | exact 0].
Qed.

(* Exercise 7 *)

Definition mod2 : nat → bool.
Proof.
  intros n.
  induction n as [| p hp].
  - exact false.
  - exact (not hp).
Defined.  

Compute (mod2 15).
(* Should be true (aka 1) *)
Compute (mod2 20).
(* Should be false (aka 0) *)

(* Exercise 8 *)

Definition mult : nat → nat → nat.
Proof.
  intros n m.
  induction m as [| p hp].
  - exact 0.
  - exact (add hp n).
Defined.   

Compute (mult 2 3).

(* Exercise 9 *)

Definition leq : nat → nat → bool.
Proof.
  intros n.
  induction n as [| p hp].
  - intros m.
    exact true.
  - intros m.
    induction m as [| q hq].
  -- exact false.
  -- exact (hp q).     
Defined.

Compute (leq 0 0).
Compute (leq 0 1).
Compute (leq 1 0).
Compute (leq 1 1).
Compute (leq 1 2).
Compute (leq 2 1).
Compute (leq 2 3).
Compute (leq 3 2).
      
(* Exercise 10 *)

Theorem leqrefl : ∏ (n : nat) , boolRep (leq n n).
Proof.
  intro n.
  induction n as [| p hp].
  - exact tt.
  - exact hp.
Qed.  


(* Exercise 11 *)

(* 
Define ≤ inductively as:
Inductive leqUU : nat → nat → UU := ...
*)

Inductive leqUU : nat -> nat -> UU :=
| leqUUrefl : forall x : nat, leqUU 0 x 
| leqUUsucc : forall x y : nat, leqUU x y -> leqUU (S x) (S y)
.

Theorem leqbooltotype : ∏ (n m : nat) , boolRep (leq n m) → leqUU n m.
Proof.
  intros n.
  induction n as [| p hp].
  - intros m h1.
    exact (leqUUrefl m).
  - intros m.
    induction m as [| q hq].
  -- simpl.
     intros []. 
  -- simpl.
     intros h1.
     apply leqUUsucc.
     apply hp.
     exact h1.
Qed.