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

Lemma functionext_equiv {A : UU} {B : A → UU} {f f' : ∏ a : A, B a} : 
  (f = f') ≃ (∏ a : A, f a = f' a).
Proof.
  use tpair.
  apply toforallpaths.
  simpl.
  apply isweqtoforallpathsAxiom.
Qed.

Lemma functionex_eq {A : UU} {B : A → UU} (f f' : ∏ a : A, B a) : 
(f = f') = (∏ a : A, f a = f' a).
Proof.
  apply univalence.
  apply functionext_equiv.
Qed.

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
  rewrite (functionex_eq g g').
  apply impred_isaprop.
  intro a.
  apply f.
Qed.

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
  g ∘ f ~ idfun S
  ×
  f ∘ g ~ idfun T.

Definition set_idtoiso (S T : hSet) : (S = T) → (setiso S T).
Proof.
  intro e.
  induction e.
  use tpair.
  - exact (idfun S).
  - use tpair.
    + exact (idfun S).
    + split.
      * intro s.
        simpl.
        apply idpath.
      * intro s.
        simpl.
        apply idpath.
Defined.

Theorem set_univalence (S T : hSet) : isweq (set_idtoiso S T).
Proof.
  Admitted.
  (* You don't have to fill this proof in; it is from previous exercises.*)

Definition z_iso_to_setiso (a b : set_category) : z_iso a b → setiso a b.
Proof.
  intros [f [g [h1 h2]]].
  exists f.
  exists g.
  split.
  {
    apply toforallpaths.
    exact h1.
  }
  {
    apply toforallpaths.
    exact h2.
  }
Defined.

Definition setiso_to_z_iso (a b : set_category) : setiso a b → z_iso a b.
Proof.
  intros [f [g [h1 h2]]].
  exists f.
  exists g.
  split.
  {
    apply funextsec.
    exact h1.
  }
  {
    apply funextsec.
    exact h2.
  }
Defined.

Lemma setiso_eq_z_iso (a b : set_category) : isweq (setiso_to_z_iso a b).
Proof.
  induction a as [A ha].
  induction b as [B hb].
  intros [f [g h]].
  use isweq_iso.
  {
    apply z_iso_to_setiso.
  }
  {
    intros [f' [g' [h']]].
    unfold setiso_to_z_iso.
    unfold z_iso_to_setiso.
    use total2_paths2_f. apply idpath. cbn.
    use total2_paths2_f. apply idpath. cbn.
    use total2_paths2_f;
    apply funextsec;
    intro x;
    [apply ha | apply hb].
  }
  {
    intros [f' [g' [h']]].
    unfold z_iso_to_setiso.
    unfold setiso_to_z_iso.
    use total2_paths2_f. apply idpath. cbn.
    use total2_paths2_f. apply idpath. cbn.
    use total2_paths2_f;
    apply isaset_commutes_Π;
    intros;
    [apply ha | apply hb].
  }
Qed.

Lemma composition_idtoiso (a b : set_category) : 
  @idtoiso _ a b = setiso_to_z_iso a b ∘ set_idtoiso a b.
Proof.
  apply funextsec.
  intros [].
  simpl.
  unfold setiso_to_z_iso.
  use total2_paths2_f. apply idpath. cbn.
  use total2_paths2_f. apply idpath. cbn.
  use total2_paths2_f;
  apply isaset_commutes_Π;
  intros;
  induction a as [A ha];
  exact ha.
Qed.

Theorem set : univalent_category.
Proof.
  exists set_category.
  unfold is_univalent.
  intros a b.
  rewrite composition_idtoiso.
  apply twooutof3c.
  apply set_univalence.
  apply setiso_eq_z_iso.
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