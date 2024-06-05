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

Print isapropimpl.
Print isweqimplimpl.

Definition fun4 {T : UU} {P : hProp} : (T → P) → (prop_trunc T → P).
Proof.
  intro f.
  intro h.
  unfold prop_trunc in h.
  apply h.
  exact f.
Defined.

Definition inv4 {T : UU} {P : hProp} : (prop_trunc T → P) → (T → P).
Proof.
  intro f.
  intro t.
  apply f.
  unfold prop_trunc.
  intro P'.
  intro g.
  apply g.
  exact t.
Defined.

Theorem univ_prop_prop_trunc (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Proof.
  exists fun4.
  use isweq_iso.
  {
    exact inv4.
  }
  {
    intro g.
    apply funextsec.
    intro t.
    unfold fun4.
    unfold inv4.
    apply idpath.
  }
  {
    intro g.
    apply funextsec.
    intro t.
    induction P as [P hP].
    simpl in *.
    apply hP.
  }
Qed.

Theorem univ_prop_prop_trunc' (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Proof.
  exists fun4.
  apply isweqimplimpl.
  {
    apply inv4.
  }
  {
    apply isapropimpl.
    induction P as [P hP]. simpl in *.
    exact hP.
  }
  {
    apply isapropimpl.
    induction P as [P hP]. simpl in *.
    exact hP.
  }
Qed.

Definition eq {X Y : UU} (f g : X → Y) : isaprop Y → f = g.
Proof.
  intro h.
  apply funextsec.
  intro x.
  apply h.
Qed.

Theorem isaprop_to_irrelevance {P : UU} : isaprop P → (∏ x y : P, x = y).
Proof.
  intros h x y.
  induction (h x y) as [c _].
  exact c.
Qed.

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Theorem irrelevance_to_isaprop {P : UU} : (∏ x y : P, x = y) → isaprop P.
Proof.
  intros h x y.
  apply (hlevel_cumulative).
  exists y.
  intro t.
  apply h.
Qed.

Theorem isapropimpl' {X Y: UU}: isaprop Y → isaprop (X → Y).
Proof.
  intro h.
  intros f g.
  apply irrelevance_to_isaprop.
  intros f' g'.
  apply funextsec.
  intro x.
  apply h.
Qed.


(* Exercise 5 *)

(* Show that hProp is a Set. *)

(* Hint: use ~weqtopaths~, ~isapropweqtoprop~, ~subtypeInjectivity~, and ~isapropisofhlevel~. *)

Theorem hProp_is_Set : isaset hProp.
Proof.
  intros [X h] [X' h'].
  assert (isaprop (X ≃ X') → isaprop (X = X')).
  {
    assert ((X = X') = (X ≃ X')).
    {
      apply ua.
      exists eqweqmap.
      apply ua.
    }
    intro h1.
    rewrite !X0.
    exact h1.
  }
  assert ((X,, h = X',, h') = (X = X')).
  {
    apply weqtopaths.
    apply subtypeInjectivity.
    unfold isPredicate.
    intro A.
    apply isapropisofhlevel.
  }
  apply (transportf isaprop (!X1)).
  apply X0.
  apply isapropweqtoprop.
  exact h'.
Qed.

