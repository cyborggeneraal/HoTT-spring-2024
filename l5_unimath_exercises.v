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

Theorem equiv_pres_contract {A B : UU} : A ≃ B → iscontr A → iscontr B.
Proof.
  intros [f weq_f] [a ha].
  exists (f a).
  intro b.
  induction (weq_f b) as [[c []] _].
  apply maponpaths.
  apply ha.
Qed.

(* These proofs are starting to get more complicated, so you might want to the tactics `assert` or `transparent assert`. They basically let you prove small lemmas within your proof. If the lemma is not very small, I recommend making it a real lemma outside of your proof.*)
(* For assert you type 
`assert (x : T).`
where T is some specific type that you want to prove. Then a new goal (T) will be added, and you can open that goal by using the bullets (i.e. `-`, `+`, etc) or by putting the proof in curly braces. Once you are done, you can move back to the original goal by using the same kind of bullet or closing the curly braces, and then x : T will be added to the list of hypotheses.*)
(* If you want to use something about how x was constructed in the proof that follows, then you need `transparent assert`. Type:
`transparent assert (x : (T)).`
Note the extra parentheses.
*)

(* Exercise 3 *)
Theorem equiv_fam_iff_equiv_tot {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x) :
  (∏ x : A, isweq (f x)) <-> isweq (tot f).
Proof.
  split.
  - intro weq_fx.
    intros y.
    apply (@equiv_pres_contract (hfiber (f (pr1 y)) (pr2 y))).
  -- apply weqinvweq.
     apply equiv_fib. 
  -- induction y as [a c].
     unfold isweq in weq_fx.
     simpl.
     exact (weq_fx a c).
  - intros weq_totf a y.
    eapply (equiv_pres_contract _ (weq_totf (a,, y))).
    Unshelve.
    apply equiv_fib.
Qed.
    
(* Show Theorem 11.1.3 of Rijke. *)

(* Exercise 4 *)

(* Show Thm 11.4.2 of Rijke. *)

Definition isemb {A B : UU} (f : A → B) :=
  ∏ x y : A, isweq (@maponpaths A B f x y).

Theorem equiv_is_embed {A B : UU} :
  ∏ f : A → B, isweq f → isemb f.
Proof.
  intros f h x.
  assert (f' := λ y : A, @maponpaths _ _ f x y).
  apply (pr2 (equiv_fam_iff_equiv_tot f')).
  
  