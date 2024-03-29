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
  intro a'.
  exact a.
Qed.

Theorem Ex_9_2_a (b : bool) : isweq (const b).
Proof.
  Admitted.

(* 1c. Exercise 9.4a *)
Definition has_retract {A B : UU} (f : A → B) : UU := ∑ g : B → A, g ∘ f ~ idfun A.

Theorem Ex_9_4_a {A B X : UU} (f : A → X) (g : B → X) (h : A → B)
  (H : f ~ g ∘ h) : ∑ s : B → A, h ∘ s ~ idfun B → 
  f ∘ s ~ g × 
  (has_retract f <-> has_retract g).
Proof.
  Admitted.

(* 1d. Exercise 9.9a *)
Definition repeated_composition {X : UU} (f : X → X) (n : nat) : X → X.
Proof.
  induction n as [| p f'].
  {
    exact (idfun X).
  }
  {
    exact (f' ∘ f).
  }
Defined.

Definition is_finitely_cyclic {X : UU} (f : X → X) : UU :=
  ∏ x y : X, ∑ k : nat, repeated_composition f k x = y.

Theorem Ex_9_9_a {X : UU} {f : X → X} (h : is_finitely_cyclic f) :
  isweq f.
Proof.
  Admitted.

(**************************************************************)

(* For the following exercises you can use the following results from previous exercise sessions without proofs. 
  You can also use `isweq_iso` and `funextsec` from the library.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

(* From here on, all `Admitted.`s should be filled in with proofs. As always, don't change the statements of any Theorems below, but you can always prove extra Lemmas to help. *)

(* Exercise 2 *)

(* Show that the definitions of proposition are equivalent. *)

Definition isaprop_to_irrelevance {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intros h x y.
  induction (h x y) as [c _].
  exact c.
Defined.

Definition irrelevance_to_isaprop {P : UU} : (∏ x y : P, x = y) → (isaprop P).
Proof.
  intros h x' y'.
  apply (@hlevel_cumulative 0).
  simpl.
  exists y'.
  intro t.
  exact (h t y').
Defined.

Lemma iscontr_iscontr {A : UU} : iscontr A → iscontr (iscontr A).
Proof.
  intros [c hc].
  exists (c,, hc).
  intros [c' hc'].
  induction (hc' c).
  assert (hc' = hc).
  {
    apply funextsec.
    intro x.
    assert (H := @hlevel_cumulative 1 A (@hlevel_cumulative 0 A (c,, hc))).
    apply (isaprop_to_irrelevance (H x c)).
  }
  induction X.
  apply idpath.
Qed.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  exists isaprop_to_irrelevance.
  apply (isweq_iso isaprop_to_irrelevance irrelevance_to_isaprop).
  - intro h.
    apply funextsec; intro x.
    apply funextsec; intro y.
    induction (iscontr_iscontr (h x y)) as [c hp].
    exact (hp (irrelevance_to_isaprop (isaprop_to_irrelevance h) x y) @ !hp (h x y)).
  - intros f.
    assert (H := hlevel_cumulative (irrelevance_to_isaprop f)).
    simpl in H.
    apply funextsec.
    intro x'.
    apply funextsec.
    intro y'.
    apply (H x' y').
  Qed.

(* Exercise 3 *)

Search "invmap".

(* Proposition 12.1.4 from Rijke: An equivalence between propositions is (logically equivalent to) a logical equivalence. *)

Theorem Prop_12_1_4 (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
Proof.
  split.
  - intros [f hf].
    split.
  -- exact f.
  -- intro q.
     induction (hf q) as [c _].
     induction c as [p _].
     exact p.
  - intros [f g].
    exists f.
    eapply (isweq_iso f g).
  -- intro x.
     induction P as [P hp]; simpl in *.
     apply hp.
  -- intro y.
     induction Q as [Q hq]; simpl in *.
     apply hq.
Qed.

(* Exercise 4 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  apply irrelevance_to_isaprop.
  intros f g.
  apply funextsec; intro x.
  apply isaprop_to_irrelevance.
  apply p.
Qed.

Lemma prop_commutes_fun {A : UU} {B : hProp} : isaprop (A → B).
Proof.
  apply prop_commutes_Π.
  induction B as [B hb]; simpl in *.
  intro x.
  exact hb.
Qed.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  apply irrelevance_to_isaprop.
  intros p q.
  unfold isweq in *.
  apply funextsec; intro x.
  apply isaprop_to_irrelevance.
  apply hlevel_cumulative.
  simpl.
  apply iscontr_iscontr.
  exact (p x).
Qed.

(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

Definition prop_equiv_to_lequiv {P Q : hProp} : (P ≃ Q) → (P <-> Q).
Proof.
  intro h.
  split.
  - induction h as [f _].
    exact f.
  - intro q.
    induction h as [f hf].
    induction (hf q) as [[p _] _].
    exact p. 
Defined.

Definition prop_lequiv_to_equiv {P Q : hProp} : (P <-> Q) → (P ≃ Q).
Proof.
  intros [f g].
  exists f.
  apply (isweq_iso f g).
  - intro x.
    induction P as [P hp]; simpl in *.
    apply hp.
  - intro y.
    induction Q as [Q hq]; simpl in *.
    apply hq.
Defined.

Lemma prop_commutes_prod {A B : UU} : isaprop A → isaprop B → isaprop (A × B).
Proof.
  intros h1 h2.
  apply irrelevance_to_isaprop.
  intros [x1 x2] [y1 y2].
  induction (isaprop_to_irrelevance h1 x1 y1).
  induction (isaprop_to_irrelevance h2 x2 y2).
  apply idpath.
Qed.

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  exists prop_equiv_to_lequiv.
  apply (isweq_iso prop_equiv_to_lequiv prop_lequiv_to_equiv).
  - intros h.
    induction (prop_lequiv_to_equiv (prop_equiv_to_lequiv h)) as [f hf].
    induction (h) as [f' hf'].
    induction (isaprop_to_irrelevance (prop_commutes_fun) f f').
    induction (isaprop_to_irrelevance (isweq_is_prop f) hf hf').
    apply idpath.
  - intros [f g].
    induction (prop_equiv_to_lequiv(prop_lequiv_to_equiv(f,,g))) as [f' g'].
    apply isaprop_to_irrelevance.
    apply prop_commutes_prod.
    {
      apply prop_commutes_fun.
    }
    {
      apply prop_commutes_fun.
    }
Qed.
    
    
    