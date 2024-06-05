(** * l9 Exercises *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.All.

(**                   **)
(** * Preliminaries * **)
(**                   **)

Variable funext : funextsecStatement.

(** Generalisation of [maponpaths] to dependent functions. *)
(** Called [apd] in the lecture *)
Definition maponpaths_dep {X:UU} {Y : X -> UU}
    (f : ∏ x:X, Y x) {x1 x2} (e : x1 = x2)
  : transportf _ e (f x1) = f x2.
Proof.
  induction e. apply idpath.
Defined.

(** A circle is something that looks like a circle! *)
Definition circle_ind_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
  (* The dependent function *)
   ∑ (f : ∏ x:S, Y x)
  (* The computation rule for the basepoint *)
     (e_b : f b = y_b),
  (* The computation rule for the loop, note that
     some paths have been added for it to typecheck *)
       maponpaths_dep f l
     = maponpaths _ e_b @ y_l @ !e_b.

(** From now on, we fix a circle type *)
Context {S1 : UU} {base : S1} (loop : base = base)
  (circle_str : circle_ind_structure loop).

(* For ease of use, we provide "accessors" to the relevant data *)
Definition circle_ind
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : ∏ x:S1, Y x.
Proof.
  exact (pr1 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_base
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : circle_ind y_l base = y_b.
Proof.
  exact (pr12 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_loop
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : maponpaths_dep (circle_ind y_l) loop
  = maponpaths _ (circle_ind_comp_base _)
    @ y_l @ ! (circle_ind_comp_base _).
Proof.
  exact (pr22 (circle_str _ _ y_l)).
Defined.

(**                   **)
(** * Exercises     * **)
(**                   **)

(* Exercise 1 *, The uniqueness principle *)
(* Hint: you may need [pathscomp0rid] and you will need
   to state your own lemma(s) *)

Lemma general_circ_uniq
    {Y X : UU} {x x' : X} {l : x = x'} {f g : X -> Y}
    (p : f x = g x) :
    transportf (λ x, f x = g x) l p = !maponpaths f l @ p @ maponpaths g l.
Proof.
  induction l.
  simpl.
  cbn.
  rewrite pathscomp0rid.
  apply idpath.
Qed.

Theorem transport_f_g
    {A B : UU} {f g : A -> B} {x y : A} (l : x = y) (r : f x = g x)
  : transportf (λ x : A, f x = g x) l r = !(maponpaths f l) @ r @ maponpaths g l.
Proof.
  induction l.
  cbn.
  rewrite pathscomp0rid.
  apply idpath.
Qed.

Theorem transport_id_id
    {A : UU} {x y : A} (l : x = y) (r : x = x)
  : transportf (λ x : A, x = x) l r = !l @ r @ l.
Proof.
  induction l.
  cbn.
  rewrite pathscomp0rid.
  apply idpath.
Qed.

Definition circle_uniq
    {Y : UU} {f g : S1 -> Y}
    (p : f base = g base)
    (q : transportf (λ x, x = x) p (maponpaths f loop) = maponpaths g loop) :
    ∏ (x : S1), f x = g x.
Proof.
  apply (@circle_ind _ p).
  rewrite transport_f_g.
  set (H := transport_id_id p (maponpaths f loop)).
  rewrite H in q.
  clear H.
  rewrite <- q.
  
  assert (H' : ∏ {x y z w : Y} (p : x = y) (q : x = z) (r: y = w),
    !p @ q @ !q @ p @ r = r).
  {
    intros x y z w [] [] [].
    apply idpath.
  }
  apply (H' _ _ _ _ (maponpaths f loop) p p).
Qed.

(* Exercise 2 *, The non-dependent induction principle *)
(* Hint, you will probably need [transportf_const] and [eqtohomot] *)

Definition circle_rec
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : S1 → Y.
Proof.
  apply (@circle_ind (λ _, Y) y_b).

  assert (H : ∏ (x x' : S1) (l : x = x'),
    transportf (λ _ : S1, Y) l y_b = y_b).
  {
    intros x x' l.
    induction l.
    cbn.
    apply idpath.
  }
  apply H.
Defined.

Definition circle_rec_comp_base
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : circle_rec y_l base = y_b.
Proof.
  unfold circle_rec.
  apply (circle_ind_comp_base (
    (paths_rect S1 base (λ (x' : S1) (l : base = x'), transportf (λ _ : S1, Y) l y_b = y_b) (idpath y_b) base loop))
  ).
Qed.

(* Hint, you will need a coherence lemma *)
Definition circle_rec_comp_loop
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : maponpaths (circle_rec y_l) loop
  = circle_rec_comp_base y_l @ y_l @ ! circle_rec_comp_base y_l.
Proof.
Admitted.


(* Exercise 3 *, The universal principle *)
(* Hint: Use the above exercises and [total2_paths2_f] *)

Definition circle_ump_structure (Y : UU) :
  isweq ((fun f => (f base,, maponpaths f loop)) : (S1 -> Y) -> (∑ y:Y, y = y)).
Proof.
Admitted.

(* Exercise 4 *, The suspension HIT *)
(* Give a definition of the suspension HIT as was done above for the circle *)

Definition ΣA_ind_structure (A S : UU) (north south : S) (p : A → north = south) : UU
  := ∏ (Y : S → UU) (y_n : Y north) (y_s : Y south) (y_p : ∏ a : A, transportf _ (p a) y_n = y_s),
  ∑ (f : ∏ s: S, Y s)
  (e_n : f(north) = y_n) (e_s : f(south) = y_s), 
  ∏ a : A,  
    maponpaths_dep f (p a)
    = (maponpaths (transportf _ (p a)) e_n) @ y_p a @ ! e_s.

Check transportf.
