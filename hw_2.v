Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Formulate the following statements from Rijke in type theory (you do not have to prove them). The answer to the first one (a) is given as an example. *)

(* 1a. Theorem 9.3.4 *)

Definition Eq_Σ {A : UU} {B : A → UU}: (∑ x : A, B x) → (∑ x : A, B x) → UU.
Proof.
  Admitted.

Definition pair_eq {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : (s = t) → Eq_Σ s t.
Proof.
  Admitted.

Theorem Thm_9_3_4 {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : isweq (pair_eq s t).
Proof.
  Admitted.

(* 1b. Exercise 9.2a *)
Definition const {A : UU} (a : A) : A → A.
Proof.
  Admitted.

Theorem Ex_9_2_a (b : bool) : isweq (const b).
Proof.
  Admitted.

Search "retract".

(* 1c. Exercise 9.4a *)
Definition has_retract {A B : UU} (f : A → B) : UU := ∑ g : B → A, g ∘ f ~ idfun A.

Theorem Ex_9_4_a {A B X : UU} (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ g ∘ h) : ∑ s : B → A, h ∘ s ~ idfun B → 
  f ∘ s ~ g × 
  (has_retract f <-> has_retract g).
Proof.
  Admitted.

(* 1d. Exercise 9.9a *)

(**************************************************************)

(* For the following exercises you can use the following results from previous exercise sessions without proofs. 
  You can also use `isweq_iso` and `funextsec` from the library.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  induction h as [c h].
  exact (h x @ ! h y).
Qed.

(* From here on, all `Admitted.`s should be filled in with proofs. As always, don't change the statements of any Theorems below, but you can always prove extra Lemmas to help. *)

(* Exercise 2 *)

(* Show that the definitions of proposition are equivalent. *)

Search "isweq".

Definition f2 {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intros h x y.
  induction (h x y) as [c _].
  exact c.
Defined.

Definition f2' {P : UU} : (∏ x y : P, x = y) → (isaprop P).
Proof.
  intros h x y.
  simpl.
  apply (@hlevel_cumulative 0).
  simpl.
  exists y.
  intro t.
  exact (h t y).
Defined.


Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  exists f2.
  apply (isweq_iso f2 f2').
  - intro h.
    unfold f2.
    unfold f2'.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    unfold isaprop in h.
    simpl in h.
    apply (isapropisofhlevel 0 (x = y)).
  - intros f.
    assert (H := hlevel_cumulative (f2' f)).
    simpl in H.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    apply (H x y).
  Qed.

(* Exercise 3 *)

Search "invmap".

(* Proposition 12.1.4 from Rijke: An equivalence between propositions is (logically equivalent to) a logical equivalence. *)

Theorem Prop_12_1_4 (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
Proof.
  split.
  - intros h.
    split.
  -- induction h as [f _].
     exact f.
  -- exact (invmap h).
  - intros [f g].
    exists f.
    eapply (isweq_iso f g).
  -- intro x.
     induction P as [P hp].
     simpl in *.
     apply hp.
  -- intro y.
     induction Q as [Q hq].
     simpl in *.
     apply hq.
Qed.

(* Exercise 4 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  apply f2'.
  intros f g.
  apply funextsec.
  intro x.
  apply f2.
  apply p.
Qed.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Lemma ex5 {A B : UU} {f : A → B} {y : B} {c : hfiber f y} (h1 h2 : ∏ t : hfiber f y, t = c) :
  h1 = h2.
Proof.
  apply funextsec.
  intro x.
  apply contr_to_path.
  exists (h1 x).
  intro t.
  induction t.
Admitted.


Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  apply f2'.
  intros p q.
  unfold isweq in *.
  apply funextsec.
  intro x.
  induction (p x) as [c hp].
  induction (q x) as [c' hq].
  induction (hq c).
  induction (ex5 hp hq).
  apply idpath.
Qed.

(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

Definition f6 {P Q : hProp} : (P ≃ Q) → (P <-> Q).
Proof.
  intro h.
  split.
  - induction h as [f _].
    exact f.
  - exact (invmap h).
Defined.

Definition f6' {P Q : hProp} : (P <-> Q) → (P ≃ Q).
Proof.
  intros [f g].
  exists f.
  apply (isweq_iso f g).
  - intro x.
    induction P as [P hp].
    simpl in *.
    apply hp.
  - intro y.
    induction Q as [Q hq].
    simpl in *.
    apply hq.
Defined.

Lemma char_pair {A : UU} {B : A → UU} {a : A} {b b' : B a} : 
  b = b' → (a ,, b) = (a ,, b').
Proof.
  intros [].
  apply idpath.
Qed. 

Lemma char_pair_fst {A : UU} {B : A → UU} {a a' : A} {b : B a} {b' : B a'} 
  : (a,, b) = (a',, b') → a = a'.
Proof.
  intros e.
  apply (@maponpaths (∑ a : A, B a) A pr1 (a,, b) (a' ,, b')).
  exact e.
Qed.

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  exists f6.
  apply (isweq_iso f6 f6').
  - intros h.
    apply contr_to_path.
    exists h.
    intro t.
    Search "isaprop_total".
    unfold weq in h.
    assert (isaprop (P -> Q)).
  -- apply prop_commutes_Π.
     intro p.
     induction Q as [Q hq].
     simpl.
     exact hq.
  -- induction (isaprop_total2 ((P → Q),, X) (λ x, (isweq x,, isweq_is_prop x)) t h) as [c _].
     exact c. 
  - intros [h1 h2].
    unfold f6'.
    unfold f6.
    unfold invmap.
    simpl.
    apply idpath.
  Qed.
    
    
    