Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Exercise 1 *)

(* Show that the propositional truncation of the booleans is the unit type. *)

(* Hint: use `funextsec`. *)

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Definition prop_trunc_bool_to_unit : prop_trunc bool -> unit.
Proof.
  intro f.
  exact tt.
Defined.

Definition unit_to_prop_trunc_bool : unit -> prop_trunc bool.
Proof.
  intro t.
  intro P.
  intro f.
  apply f.
  exact true.
Defined.

Theorem ex_1 : prop_trunc bool ≃ unit.
Proof.
  exists prop_trunc_bool_to_unit.
  use isweq_iso.
  {
    exact unit_to_prop_trunc_bool. 
  }
  {
    intro h.
    apply funextsec.
    intro P.
    apply funextsec.
    intro f.
    induction P as [P hP].
    simpl in *.
    apply proofirrelevance.
    exact hP.
  }
  {
    intro y.
    apply proofirrelevance.
    exact isapropunit. 
  }
Qed.

(* Exercise 2 *)

(* Define the `singleton' univalent category: the category with one object and no nonidentity arrows.*)

Definition singleton_precategory_ob_mor : precategory_ob_mor.
Proof.
  unfold precategory_ob_mor.
  exists unit.
  intros a b.
  exact unit.
Defined.

Definition singleton_precategory_data : precategory_data.
Proof.
  unfold precategory_data.
  exists singleton_precategory_ob_mor.
  unfold precategory_id_comp.
  unfold singleton_precategory_ob_mor.
  simpl.
  split.
  {
    intro c.
    exact tt. 
  }
  {
    intros a b c f g.
    exact tt. 
  }
Defined.

Definition singleton_precategory : precategory.
Proof.
  unfold precategory.
  exists singleton_precategory_data.
  unfold is_precategory.
  repeat split; repeat intros; 
  apply isapropunit.
Defined.

Definition singleton_category : category.
Proof.
  unfold category.
  exists singleton_precategory.
  unfold has_homsets.
  intros a b.
  unfold singleton_precategory.
  simpl.
  exact isasetunit.
Defined.

Lemma dom_cod_contr_map_contr {A B : UU} : ∏ f : A -> B, iscontr A -> iscontr B -> isweq f.
Proof.
  intros f ha hb.
  induction ha as [ca ha].
  induction hb as [cb hb].
  intro b.
  use tpair.
  {
    exists ca.
    rewrite (hb b).
    rewrite (hb (f ca)).
    apply idpath. 
  }
  simpl.
  intro t.
  induction t as [a h].
  use total2_paths2_f.
  {
    apply ha. 
  }
  {
    induction (ha a).
    cbn.

    simpl.
    rewrite <- h. 
  }
  Admitted.

Lemma is_z_isomorphism_isaprop (a b : singleton_category) 
  (f : singleton_category ⟦ a, b ⟧) : isaprop (is_z_isomorphism f).
  apply isapropifcontr.
  unfold is_z_isomorphism.
  Admitted.


Definition singleton_uni_category : univalent_category.
Proof.
  unfold univalent_category.
  exists singleton_category.
  {
    simpl.
    unfold is_univalent.
    intros a b.
    use isweq_iso. {intros; apply isapropunit. }
    {
      intro x.
      apply isasetunit. 
    }
    {
      intro y.
      enough (h : isProofIrrelevant (z_iso a b)). {apply h. }
      intros [f hf] [g hg].
      use total2_paths2_f.
      {
        apply isapropunit. 
      }
      {

      } 
    }
    simpl in *.
    unfold singleton_category in *.
    
    assert (iscontr (@z_iso singleton_precategory_data tt tt)).
    {
      unfold z_iso.
      use tpair.
      {
        unfold singleton_precategory_data.
        simpl in *.
        exists tt.
        unfold is_z_isomorphism.
        simpl.
        exists tt.
        unfold is_inverse_in_precat.
        split; apply isapropunit. 
      }
      simpl.
      intro t.
      induction t as [f hf].
      use total2_paths2_f.
      {
        apply isapropunit. 
      }
      {
        cbn.
        induction f.
        assert (isProofIrrelevantUnit tt tt = idpath tt).
        {
          apply isasetunit. 
        }
        rewrite X.
        clear X.
        cbn.
        induction hf as [f hf].
        simpl in *.
        induction f.
        use total2_paths2_f.
        apply idpath.
        cbn.
        induction hf as [h1 h2].
        cbn in *.
        use total2_paths2_f.
        {
          apply isasetunit. 
        }
        {
          apply isasetunit.
        }
      }
    }
    use isweqcontrcontr.
    {
      apply isapropunit. 
    }
    {
      apply X. 
    }
  }
Qed.

(* I.e., define a term of `univalent_category`, defined in the library.*)

(* Hint: exercises 2 and 3 are very similar. Think about lemmas to use so that you don't have to duplicate your work. *)

(* Exercise 3 *)

(* Define the `walking isomorphism' precategory: that is a category whose underlying set is the booleans and such that true ≅ false.
*)

(* I.e., define a term of type `category`. Unimath uses category to mean what the HoTT book calls precategory.*)

(* Exercise 4 *)

(* Show that the Rezk completion of the category from exercise 3 is the category from exercise 2.*)

(* I.e. construct a term of type `weak_equiv C D` where C and D are the categories defined above.*)

Definition weak_equiv (C D : category) : UU := ∑ H : functor C D, essentially_surjective H × fully_faithful H.