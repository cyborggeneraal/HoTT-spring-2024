Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Show Lemma 11.1.2 of Rijke. Give Def 11.1.1 yourself. *)

Definition tot {A : UU} {B C : A -> UU} 
  (f : ∏ x : A, B x -> C x) :
  (∑ x : A, B x) -> (∑ x : A, C x).
Proof.
  intros [x y].
  exact (x,, f x y).
Defined.

Theorem equiv_fib {A : UU} {B C : A -> UU}
  (f : ∏ x : A, B x -> C x) (t : ∑ x : A, C x) :
  hfiber (tot f) t ≃ hfiber (f (pr1 t)) (pr2 t).
Proof.
  use tpair.
  - simpl.
    intros [[x' y'] p].
    use tpair.
  -- unfold tot in p.
     induction p.
     simpl.
     exact y'.
  -- unfold tot in p.
     simpl.
     induction p.
     simpl.
     apply idpath.
  - simpl.
    use isweq_iso.
  -- intros [x' h].
     use tpair.
  --- induction t as [t1 t2].
      simpl in x'.
      exact (t1,, x'). 
  --- induction t as [t1 t2].
      simpl in *.
      unfold tot.
      induction h.
      apply idpath.
  -- intros [x y].
     unfold tot in y.
     induction y.
     simpl.
     induction x as [x1 x2].
     apply idpath.
  -- intros [x y].
     induction t as [t1 t2].
     simpl in *.
     induction y.
     simpl.
     apply idpath.
   Qed.

(* Hint: Follow the proof in Rijke, using `isweq_iso` at the end. For the statements, you will want to use `hfiber`, `∘` (`funcomp`), `~` (`homot`), `≃` (`weq`). *)

(* Exercise 2 *)

(* Show that if two types are equivalent and one is contractible, then the other is. *)

(* These proofs are starting to get more complicated, so you might want to the tactics `assert` or `transparent assert`. They basically let you prove small lemmas within your proof. If the lemma is not very small, I recommend making it a real lemma outside of your proof.*)
(* For assert you type 
`assert (x : T).`
where T is some specific type that you want to prove. Then a new goal (T) will be added, and you can open that goal by using the bullets (i.e. `-`, `+`, etc) or by putting the proof in curly braces. Once you are done, you can move back to the original goal by using the same kind of bullet or closing the curly braces, and then x : T will be added to the list of hypotheses.*)
(* If you want to use something about how x was constructed in the proof that follows, then you need `transparent assert`. Type:
`transparent assert (x : (T)).`
Note the extra parentheses.
*)

(* Exercise 3 *)

(* Show Theorem 11.1.3 of Rijke. *)

(* Exercise 4 *)

(* Show Thm 11.4.2 of Rijke. *)