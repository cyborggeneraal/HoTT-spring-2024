Require Export UniMath.Foundations.All.

(* Example 1*)

(* Notes:
- idpath is the name in Unimath for refl.
- Defined as maponpaths in UniMath.Foundations.PartA.*)

(*
The identity type is defined in Unimath as:

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .
*)

Definition ap {A B : UU} (f : A → B) {x y : A} (p : x = y) : f x = f y.
Proof. 
  induction p.
  apply idpath.
Defined.

(* Example 2 *)

(* Note: this might hold definitionally based on how you defined add. If so, prove add n 0 = n instead.*)

Print add.

Definition right_unit (n : nat) : add n 0 = n.
Proof.
  induction n.
  - apply idpath.
  - simpl.
    apply ap.
    exact IHn.
Defined.

(* Example 3 *)

(* We make the parameter {A:UU} in paths explicit by writing @paths. *)

Definition reflexive {A : UU} (R: A → A → UU) : UU := ∏ a : A, a = a.

Lemma reflexive_paths (A : UU): reflexive (@paths A).
Proof.
  unfold reflexive.
  intro a.
  apply idpath.
Defined.

(* Example 4 *)

Definition symmetric {A : UU} (R: A → A → UU) : UU := ∏ (a b : A), a = b → b = a.

Lemma symmetric_paths (A : UU) : symmetric (@paths A).
Proof.
  unfold symmetric.
  intros a b.
  intro p.
  induction p.
  apply idpath.
Defined.

(* Example 5 *)

Definition transitive {A : UU} (R: A → A → UU) : UU := ∏ (a b c : A), a = b → b = c → a = c.

Lemma transitive_paths (A : UU) : transitive (@paths A).
Proof.
  unfold transitive.
  intros a b c p q.
  induction p.
  induction q.
  apply idpath.
Defined.

(* Example 6 *)

Definition equivalence {A : UU} (R: A → A → UU) : UU := (reflexive R) × (symmetric R) × (transitive R).

Theorem equivalence_paths (A : UU) : equivalence (@paths A).
Proof.
  exact (reflexive_paths A,,symmetric_paths A,,transitive_paths A).
Defined.

(* Example 7 *)

(* Everything respects equality. *)

(* Note: transport is defined as transportf in UniMath.Foundations.PartA.*)

Theorem transport {A : UU} {D : A → UU} {a b : A} (d : D a) (p: a = b) : D b.
Proof.
  induction p.
  exact d.
Defined.


(*********************************)

(* Exercise 8 *)

Theorem complicatedTransport {A : UU} {D : A → UU} {a b c : A} (p : a = b) (q : b = c) (d : D c) : D a.
Proof.
  apply (@transport A _ b a); [..| apply (symmetric_paths A _ _ p)].
  apply (@transport A _ c b); [..| apply (symmetric_paths A _ _ q)].
  exact d.
Qed.

(* Exercise 9 *)

Lemma add_S_comm : ∏ n m : nat , n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [|p hp].
  - simpl.
    apply idpath.
  - simpl.
    apply (ap S hp).
    (* apply (@transport nat (fun x:nat => S (p + S m) = S x) (p + S m) (S (p + m)));
      [..| apply hp].
    apply idpath.   *)
Qed.

Theorem add_comm : ∏ n m : nat , n + m = m + n.
Proof.
  intros n.
  induction n as [|p hp].
  - intros m.
    induction m as [|q hq]. 
  -- apply idpath.
  -- simpl.
     apply ap.
     apply (symmetric_paths nat _ _ (right_unit _)).
  - intros m.
    induction m as [|q hq].
  -- simpl.
     apply ap.
     apply right_unit.
  -- simpl.
     apply ap.
     apply (transitive_paths _ _ _ _ (add_S_comm _ _)).
     apply hq.
Qed.
    

(* Exercise 9 *)

Theorem mul_left_id : ∏ n : nat , mul 1 n = n.
Proof.
  intros n.
  apply idpath.
Qed.

(* Exercise 10 *)

Theorem succ_eq_add_one : ∏ n : nat , S n = n + 1.
Proof.
  intros n.
  induction n as [|p hp].
  - apply idpath.
  - simpl. 
    apply ap.
    exact hp.
Qed.


Theorem mul_right_id : ∏ n : nat , mul n 1 = n.
Proof.
  intros n.
  induction n as [|p hp].
  - apply idpath.
  - simpl.
    apply (transitive_paths _ _ _ _ (symmetric_paths _ _ _ (succ_eq_add_one _))).
    apply ap.
    exact hp.  
Qed.

(* Exercise 11 *)

Theorem mul_zero : ∏ (n : nat), n * 0 = 0.
Proof.
  intros n.
  induction n as [| p hp].
  - apply idpath.
  - simpl.
    induction (symmetric_paths _ _ _ (right_unit (p*0))).
    apply hp.
Qed.  

Theorem mul_succ : ∏ (n m : nat), n * S m = n * m + n.
Proof.
  intros n m.
  induction n as [| p hp].
  - apply idpath.
  - simpl.  

Theorem mul_comm : ∏ (n m : nat), n * m = m * n.
Proof.
  intros n m.
  induction n as [| p hp].
  - simpl.
    exact (! (mul_zero m)).
  - simpl.
    induction ()   

(* Define what is means to be divisible by 2 and divisible by 4, and show that being divisible by 4 implies being divisible by 2. *)
Inductive divisibleBy (d : nat) : nat -> UU :=
  Divides : ∏ n : nat, (∑ m : nat, d * m = n) -> divisibleBy d n.
    
Theorem div_by_4_imp_div_by_2 : ∏ n : nat, divisibleBy 4 n -> divisibleBy 2 n.
Proof.
  intros n h.
  induction h as [n h].
  induction h as [m h].
  apply Divides.
  exists (2 * m).
  simpl. 