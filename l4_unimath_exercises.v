
Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Define neg_neg_bool from Example 9.1.3 in R. (Note that we need to replace the hyphen with an underscore because Coq does not accept hyphens. *)

(* Remember that you can write e.g. ~Locate "~".~ to find information about notation and ~Print negb.~ or ~About negb.~ to find information about a predefined term. *)

Theorem neg_neg_bool: negb ∘ negb ~ idfun bool.
Proof.
  intros [ | ]; apply idpath.
Qed.

(* Exercise 2 *)

(* Define concat_htpy from Def 9.1.5 in R.*)
Definition concat_htpy {A : UU} {B : A -> UU} 
    {f g h : ∏ x : A, B x} :
    f ~ g -> g ~ h -> f ~ h.
Proof.
    intros G H x.
    exact ((G x)@(H x)).
Defined.


Infix "~@~" := concat_htpy (at level 70, no associativity).

(* This defines infix notation for concatenation. The stuff in parentheses is not important, but tells Coq the order of operations when it is used in combination with other infix notation.*)

(* Exercise 3 *)

Search "path".

(* Define assoc_htpy from Prop 9.1.6 in R. *)
Definition assoc_htpy {A B : UU}
    {f g h p : A -> B}
    {G : f ~ g} {H : g ~ h} {K : h ~ p} :
    ((G ~@~ H) ~@~ K) ~ (G ~@~ (H ~@~ K)).
Proof.
    intro x.
    apply pathsinv0.
    apply path_assoc.
Qed.

(* Hint: use path_assoc. *)

(* Exercise 4 *)

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    exists tt.
    intros [].
    apply idpath.
Qed.

(* Exercise 5 *)

Lemma unit_is_prop (x y : unit) : iscontr (x = y).
Proof.
    induction x.
    use (tpair).
    - induction y.
      apply idpath.
    - simpl.
      intro t.
      induction t.
      apply idpath.  
Qed.
    
(* Exercise 6 *)

(* ~weq A B~ is the type of contractible maps from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    intros b.
    induction e as [f weqf].
    induction (weqf b) as [fib _].
    induction fib as [a _].
    exact a.
Qed.

(* Exericse 7 *)

(* Show Theorem 9.3.4 from R. Use ~weq~ for the notion of equivalence. You can prove this directly or use ~isweq_iso~. Solutions to both approaches are provided, so try both if you are looking for extra exercises.*)
Definition Eq_Sigma {A : UU} {B : A -> UU} (s t : ∑ x : A, B x) : UU :=
    ∑ α : pr1 s = pr1 t, transportf B α (pr2 s) = pr2 t.

Definition pair_eq {A : UU} {B : A -> UU} {s t : ∑ x : A, B x} : (s = t) ->
    Eq_Sigma s t.
Proof.
    intro hst.
    induction s as [s1 s2].
    induction t as [t1 t2].
    induction hst.
    exists (idpath s1).
    apply idpath.
Defined.

Definition eq_pair {A : UU} {B : A -> UU} {s t : ∑ x : A, B x} : 
    Eq_Sigma s t -> s = t.
Proof.
    intros [α h].
    induction s as [s1 s2].
    induction t as [t1 t2].
    simpl in α.
    induction α.
    simpl in h.
    induction h.
    apply idpath.
Defined.

Theorem pair_eq_weq {A : UU} {B : A -> UU} : ∏ s t : ∑ (x : A), B x,
    s = t ≃ Eq_Sigma s t.
Proof.
    intros [s1 s2] [t1 t2].
    exists pair_eq.
    apply (isweq_iso _ eq_pair).
    - intro x.
      induction x.
      simpl.
      apply idpath.
    - intro y.
      unfold Eq_Sigma in y.
      induction y as [α h].
      simpl in α.
      induction α.
      simpl in h.
      induction h.
      cbn.
      apply idpath.
Qed.

Theorem pair_eq_weq' {A : UU} {B : A -> UU} : ∏ s t : ∑ (x : A), B x,
    s = t ≃ @Eq_Sigma A B s t.
Proof.
    intros s t.
    use tpair. apply pair_eq. simpl.
    intro y.
    use tpair.
    - use tpair.
    -- apply eq_pair.
       exact y.
    -- simpl.
       induction y as [y hy].
       induction s as [s1 s2].
       induction t as [t1 t2].
       simpl in y.
       simpl in hy.
       induction y.
       induction hy.
       simpl.
       apply idpath.
    - simpl.
      intro x.
      simpl.
      induction x as [x hx].
      induction x.
      induction hx.
      cbn.
      apply idpath.
Qed.

      
      
      

(* Hints: - use ~transportf~.
          - cbn (similar to simpl) was necessary in my proof where sometimes simpl didn't work. 
*)

(* Exercise 8 *)

(* Every contractible type is equivalent to the unit.*)

Theorem contr_to_path {A : UU} (C : iscontr A) (x y : A) : x = y.
Proof.
    induction C as [c h].
    exact ((h x) @ !(h y)).
Qed.

Definition const {A B : UU} : A -> B -> A :=
    λ (x : A) (y : B), x.

Theorem paths_in_unit (p : tt = tt) : p = idpath tt.
Proof.
    apply contr_to_path.
    apply unit_is_prop.
Qed.
    

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    unfold weq.
    use tpair.
    - intro c.
      exact tt.
    - simpl.
      unfold isweq.
      intros [].
      unfold iscontr in *.
      induction h as [c h1].
      use tpair.
    -- unfold hfiber.
       use tpair.
    --- exact c.
    --- simpl.
        apply idpath.
    -- simpl.
       intros [x h2].
       rewrite (paths_in_unit h2).
       rewrite (h1 x).
       apply idpath.
Qed.

     
    
    