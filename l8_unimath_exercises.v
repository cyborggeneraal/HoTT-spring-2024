Require Export UniMath.Foundations.All.

(* Hint: use `isweq_iso`, `funextsec`, `total2_paths_f`, `isapropiscontr`, `proofirrelevance `, `isapropisweq`, `univalenceAxiom`, `twooutof3a`, `isapropisaset`, `isapropifcontr`. *)

(* Exercise 1 *)

Theorem ex1 {A : UU} {B : A → UU} {h : ∏ x : A, isaprop(B x)} (p p' : ∑ x : A, B x) :
    (pr1 p) = (pr1 p') ≃ (p = p').
Proof.
    use tpair.
    {
        intro e.
        induction p as [p1 p2].
        induction p' as [p1' p2'].
        simpl in *.
        induction e.
        assert (e : p2 = p2').
        {
            apply (h p1).
        }
        induction e.
        apply idpath.
    }
    {
        simpl.
        use isweq_iso.
        {
            intro e.
            apply maponpaths.
            exact e.
        }
        {
            intro e.
            induction p as [p1 p2].
            induction p' as [p1' p2'].
            simpl in *.
            induction e.
            simpl.
            induction (h p1 p2 p2') as [c hc].
            simpl.
            induction c.
            simpl.
            apply idpath.
        }
        {
            intro e.
            simpl.
            induction e.
            simpl.
            induction p as [p1 p2].
            induction (h p1 p2 p2) as [x1 x2].
            simpl.
            assert (e : x1 = idpath p2).
            {
                apply proofirrelevance.
                apply isapropifcontr.
                apply (h p1).
            }
            rewrite e.
            simpl.
            apply idpath.
        }
    }
    


(* Show that equalities of subtypes are the same as the equalities in the super types. *)

(* Exercise 2 *)

(* Show univalence for sets. *)

Definition iso (S T : UU) : UU :=
    ∑ f : S → T, 
    ∑ g : T → S,
    g ∘ f ~ idfun S ×
    f ∘ g ~ idfun T
.

Notation "S ≅ T" := (iso S T).

Definition iso_to_equiv (S T : UU) : (S ≅ T) → (S ≃ T).
Proof.
    intro H.
    induction H as [f [g [hgf hfg]]].
    exists f.
    use isweq_iso.
    {
        exact g.
    }
    {
        intro s.
        exact (hgf s).
    }
    {
        intro t.
        exact (hfg t).
    }
Defined.

Definition equiv_to_iso (S T : UU) : (S ≃ T) → (S ≅ T).
Proof.
    intro H.
    induction H as [f hf].
    exists f.
    use tpair.
    {
        intro t.
        induction (hf t) as [[s _] _].
        exact s.
    }
    {
        simpl.
        split.
        {
            intro x.
            simpl.
            induction (hf (f x)) as [[c hc] hc'].
            assert (H := maponpaths pr1 (hc' (x,, idpath (f x)))).
            simpl in *.
            induction H.
            apply idpath.
        }
        {
            intro x.
            simpl.
            unfold isweq in hf.
            induction (hf x) as [[c hc] _].
            exact hc.
        }
    }
Defined.

Lemma isaprop_commutes_pair {S : UU} {T : S → UU} : 
    isaprop S → (∏ x : S, isaprop (T x)) → isaprop (∑ x : S, T x).
Proof.
    intros hs ht.
    apply invproofirrelevance.
    intros p q.
    induction p as [p1 p2].
    induction q as [q1 q2].
    assert (e : p1 = q1).
    {
        apply hs.
    }
    induction e.
    assert (e : p2 = q2).
    {
        apply (ht p1).
    }
    induction e.
    apply idpath.
Qed.

Definition maponpaths_dependant {A : UU} {B : A → UU} {f : ∏ a : A, B a} 
    {x y : A} : ∏ e : x = y, transportf B e (f x) = f y.
Proof.
    intro e.
    induction e.
    apply idpath.
Qed.

Definition maponpaths_snd {A : UU} {B : A → UU}
    {x y : A} {x' : B x} {y' : B y} : ∏ e : (x,, x') = (y,, y'), 
    transportf B (maponpaths pr1 e) x' = y'. 
Proof.
    intro e.
    pattern (maponpaths pr1 e).
    Admitted.
    

Lemma isaset_commutes_pair {S : UU} {T : S → UU} :
    isaset S → (∏ x : S, isaset (T x)) → isaset (∑ x : S, T x).
Proof.
    intros hs ht.
    unfold isaset.
    intros p p'.
    induction p as [p1 p2].
    induction p' as [p1' p2'].
    apply invproofirrelevance.
    intros q q'.
    assert (e : p1 = p1').
    {
        assert (Q := maponpaths pr1 q); simpl in Q.
        exact Q.
    }
    induction e.
    assert (e : p2 = p2').
    {
        assert (Q := maponpaths_dependant pr2 q : transportf _ (idpath (p1,, p2)) (p1 ,, p2) = pr2 (p1,, p2')); simpl in Q.
        admit.
    }
    induction e.
    assert (H := ht p1).
    unfold isaset in H.
    assert (H' := H p2 p2).
    unfold isaprop in H'.
    simpl in H'.
    assert (Q := maponpaths pr1 q); simpl in Q.
    assert (Q' := maponpaths pr2 q : p2 = p2).
    simpl in Q.

Lemma isaset_commutes_equiv {S T : UU} : isaset S → isaset T → isaset (S ≃ T).
Proof.
    intros hs ht.
    unfold isaset in *.
    intros p q.
    induction p as [f hf].
    induction q as [g hg].

Lemma set_iso_is_equiv (S T : UU) (SH : isaset S) (TH : isaset T) : isweq(iso_to_equiv S T).
Proof.
    intro x.
    use tpair.
    {
        exists (equiv_to_iso S T x).
        admit.
    }
    Admitted.

(* Exercise 3 *)

(* Define the type of categories and univalence for categories. *)