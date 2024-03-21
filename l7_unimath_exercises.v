Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Propositional truncation is defined slightly differently in UniMath than how I defined it. Show that it has the same properties in the next few exercises. *)

Variable ua : univalenceStatement.

Variable funext : funextsecStatement.

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem prop_trunc_unit {X : UU} : X → prop_trunc X.
Proof.
  intros x P f.
  apply f.
  exact x.
Qed.

(* Exercise 2 *)

Theorem prop_trunc_unit_eq {X : UU} {x y : X} : prop_trunc_unit x = prop_trunc_unit y.
Proof.
  apply funext.
  intro P.
  apply funext.
  intro f.
  apply P.
Qed.

(* Exercise 3 *)

(* Use ~invproofirrelevance~ or what you have done before.*)

Print invproofirrelevance.
Print hProp.

Theorem prop_trunc_prop {X : UU} : isaprop (prop_trunc X).
Proof.
  use invproofirrelevance.
  unfold isProofIrrelevant.
  intros x y.
  apply funext.
  intro P.
  apply funext.
  intro f.
  apply P.
Qed.


(* Exercise 4 *)

(* Hint: use ~isapropimpl~ and ~isweqimplimpl~.*)

Print isweqimplimpl.

Theorem univ_prop_prop_trunc (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Proof.
  use tpair.
  - intros f x.
    apply x.
    exact f.
  - simpl.
    apply isweqimplimpl.
  -- intros f t.
     apply f.
     intros Q g.
     apply g.
     exact t.
  -- apply isapropimpl.
     unfold isaprop.
     simpl.
     intros x y.
     induction P as [P h].
     simpl in *.
     apply h.
  -- induction P as [P h].
     simpl.
     unfold isaprop.
     simpl.
     intros f g.
     use tpair.
  --- apply funext.
      intro x.
      apply h.
  --- simpl.
      intros [].
      unfold isaprop in *.
      simpl in *.

    


(* Exercise 5 *)

(* Show that hProp is a Set. *)

(* Hint: use ~weqtopaths~, ~isapropweqtoprop~, ~subtypeInjectivity~, and ~isapropisofhlevel~. *)

Theorem hProp_is_Set : isaset hProp.
Proof.
Admitted.

