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

Definition f2' {P : UU} : (∏ x y : P, x = y) → (isaprop P).
Proof.
  intros h x y.
  apply (@hlevel_cumulative 0).
  simpl.
  exists y.
  intro t.
  exact (h t y).
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
    apply (f2 (H x c)).
  }
  induction X.
  apply idpath.
Qed.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  exists f2.
  apply (isweq_iso f2 f2').
  - intro h.
    unfold isaprop in h.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    simpl in h.
    induction (iscontr_iscontr (h x y)) as [c hp].
    exact (hp (f2' (f2 h) x y) @ !hp (h x y)).
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
  - intros [f hf].
    split.
  -- exact f.
  -- intro q.
     induction (hf q) as [c _].
     induction c as [p _].
     exact p.
  - intros [f g].
    exists f.
    (* intro q.
    use tpair.
  -- exists (g q).
     induction Q as [Q hq]; simpl in *.
     apply (f2 hq).
  -- simpl.
     intros [t []].
     assert (e : t = g (f t)).
     {
      induction P as [P hp]; simpl in *.
      apply (f2 hp). 
     }
     induction e.
     assert (e : idpath (f t) = f2 (pr2 Q) (f t) (f t)).
     {
      induction Q as [Q hq]; simpl in *.
      assert (hq' := hlevel_cumulative hq).
      apply (f2 (hq' (f t) (f t))).
     }
     rewrite e.
     apply idpath. *)
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
  apply f2'.
  intros f g.
  apply funextsec; intro x.
  apply f2.
  apply p.
Qed.

Lemma prop_commutes_fun {A : UU} {B : hProp} : isaprop (A → B).
Proof.
  apply prop_commutes_Π.
  intro a.
  induction B as [B hb]; simpl in *.
  exact hb.
Qed.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  apply f2'.
  intros p q.
  unfold isweq in *.
  apply funextsec; intro x.
  apply f2.
  apply hlevel_cumulative.
  simpl.
  apply iscontr_iscontr.
  exact (p x).
Qed.

(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical equivalence. *)

Definition f6 {P Q : hProp} : (P ≃ Q) → (P <-> Q).
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

Lemma prop_commutes_prod {A B : UU} : isaprop A → isaprop B → isaprop (A × B).
Proof.
  intros h1 h2.
  apply f2'.
  intros [x1 x2] [y1 y2].
  induction (f2 h1 x1 y1).
  induction (f2 h2 x2 y2).
  apply idpath.
Qed.

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  exists f6.
  apply (isweq_iso f6 f6').
  - intros h.
    induction (f6' (f6 h)) as [f hf].
    induction (h) as [f' hf'].
    induction (f2 (prop_commutes_fun) f f').
    induction (f2 (isweq_is_prop f) hf hf').
    apply idpath.
  - intros [h1 h2].
    apply idpath.
Qed.
    
    
    