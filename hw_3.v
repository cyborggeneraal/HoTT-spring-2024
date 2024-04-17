Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Instructions: do Exercises 1 and 2 here in UniMath. Do Exercise 3 in LaTeX. No exercise should be done both in UniMath and LaTeX. As usual, you will submit one .v file and one .pdf file.*)

(* You can use anything proven in previous exercises or homework, and
`impred_isaprop`, `funextsec`, `weqtopaths`, `isweqtoforallpathsAxiom`, `toforallpaths`, `isweqhomot`, `twooutof3c`,
and anything else from UniMath.Foundations.UnivalenceAxiom.*)

(* Exercise 1 *)

(* Define the category of sets. *)

Definition set_ob_mor : precategory_ob_mor.
Proof.
  use tpair.
  {
    exact hSet.
  }
  intros a b.
  exact (a -> b).
Defined.

Definition set_precategory_data : precategory_data.
Proof.
  exists set_ob_mor.
  unfold precategory_id_comp.
  split.
  {
    intro C.
    unfold set_ob_mor.
    simpl.
    apply idfun.
  }
  {
    intros A B C.
    intros f g a.
    apply g.
    apply f.
    apply a.
  }
Defined.

Definition set_precategory : precategory.
Proof.
  exists set_precategory_data.
  unfold is_precategory.
  simpl.
  split; split.
  {
    intros a b f.
    apply idpath.
  }
  {
    intros a b f.
    apply idpath.
  }
  {
    intros a b c d f g h.
    apply funextsec; intro x.
    apply idpath.
  }
  {
    intros a b c d f g h.
    apply funextsec; intro x.
    apply idpath.
  }
Defined.

Lemma isaset_commutes_Π {A : UU} {B : A → UU} : 
  (∏ a : A, isaset (B a)) → isaset (∏ a : A, B a).
Proof.
  intro f.
  unfold isaset.
  intros g g'.
  Print isweqtoforallpathsAxiom.
  Print isweqtoforallpathsStatement.
  Print toforallpaths.
  Print isweq.
  Print weqtopaths.
  assert (isaprop (∏ a : A, g a = g' a)).
  {
    apply impred_isaprop.
    intro a.
    apply f.
  }
Admitted.

Theorem set_category : category.
Proof.
  exists set_precategory.
  intros [A ha] [B hb].
  apply isaset_commutes_Π.
  intro a.
  exact hb.
Defined.

(* Exercise 2 *)

(* Show that the category from exercise 1 is univalent.*)

Definition setiso (S T : hSet) : UU :=
  ∑ f : S → T ,
  ∑ g : T → S ,
  (*g ∘ f ~ idfun S*) g ∘ f = idfun S
  ×
  (*f ∘ g ~ idfun T*) f ∘ g = idfun T.

Definition set_idtoiso (S T : hSet) : (S = T) → (setiso S T).
Proof.
  intro e.
  induction e.
  use tpair.
  - exact (idfun S).
  - use tpair.
    + exact (idfun S).
    + split.
      * apply funextsec.
        intro s.
        simpl.
        apply idpath.
      * apply funextsec.
        intro s.
        simpl.
        apply idpath.
Defined.

Theorem set_univalence (S T : hSet) : isweq (set_idtoiso S T).
Proof.
  Admitted.
  (* You don't have to fill this proof in; it is from previous exercises.*)

Theorem set : univalent_category.
Proof.
  exists set_category.
  unfold is_univalent.
  intros a b.
  unfold set_category in *.
  simpl in *.
  use isweqhomot.
  {
    unfold z_iso.
    unfold set_precategory_data.
    simpl.
    unfold is_z_isomorphism.
    simpl.
    unfold is_inverse_in_precat.
    exact (set_idtoiso a b).
  }
  {
    simpl.
    intro x.
    unfold set_idtoiso.
    induction x.
    simpl.
    unfold identity_z_iso.
    use total2_paths2_f.
    {
      apply idpath.
    }
    cbn.
    unfold identity_is_z_iso.
    use total2_paths2_f.
    {
      apply idpath.
    }
    cbn.
    induction a as [A ha].
    simpl.
    assert (hfun : isaset (A → A)).
    {
      apply isaset_commutes_Π.
      intro a.
      exact ha.
    }
    use total2_paths2_f.
    {
      apply hfun.
    }
    {
      apply hfun.
    }
  }
  {
    cbn.
    apply set_univalence.
  }
Qed.

(* Exercise 3 *)

(* Do not do this one in Unimath, only in LaTeX. *)

(* Consider the category G of groupoids, and the class D ⊆ mor (G) of isofibrations. Show that this is a display map category, and that it has the two additional properties required of a display map category. That is, show that:
  i) every X → * is a display map
  ii) D is closed under isomorphisms
  iii) D is stable under pullback
  iv) D contains all isomorphisms
  v) D is closed under composition

  Use the definition for isofibration and any results from the nLab page https://ncatlab.org/nlab/show/isofibration. Hint: use Prop 3.1.
  *)