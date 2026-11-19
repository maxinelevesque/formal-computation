import FormalComputation.SKI.PermEq

/-!
# SKI: types as predicates that do not leak (the essay "Atoms and Probes")

The essay defines a type as a predicate on terms that no step changes, in either direction.
This file states that definition for SKI and checks the essay's elementary claims about it:

* conversion (steps forwards or backwards) preserves a type (`IsType.conv`);
* closing a predicate gives the least type containing it (the "Close it" control);
* a predicate defined by a probe `[ ] u` is a type when its result predicate is
  (`isType_arr`);
* the fundamental lemma for each atom: `K : A → B → A`, `I : A → A` and
  `S : (A → B → C) → (A → B) → A → C` hold semantically, for any types (`fundamental_*`).
  Only the backward direction of non-leaking is used (subject expansion);
* the rule `S K y → I` is sound: `S K y x` runs to `x` (`skRun`);
* the two runs of `K a (I b)` to `a` are counted as one run (`kaib_one_run`);
* the loop of `ω ω` as drawn in the essay (I-step in argument position first) has weight 1,
  is permutation equivalent to `omegaLoop`, and is absorbed by no continuation.

That a type is the same thing as a predicate-valued behaviour, in the sense of Theorem A, is
`beh_iff_of_subsingleton_co` in `FormalComputation/Predicates.lean`.
-/

namespace FormalComputation.SKI

/-- A **type** in the sense of the essay: a predicate that leaks along no step. -/
def IsType (P : Tm → Prop) : Prop := ∀ ⦃t u : Tm⦄, Step t u → (P t ↔ P u)

/-- **Conversion**: steps taken forwards or backwards. Two terms are converted when they lie
in one fibre. -/
def Conv : Tm → Tm → Prop := Relation.EqvGen (fun t u => Nonempty (Step t u))

/-- A type takes one value on each fibre. -/
theorem IsType.conv {P : Tm → Prop} (hP : IsType P) {t u : Tm} (h : Conv t u) :
    P t ↔ P u := by
  induction h with
  | rel _ _ h => exact hP h.some
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Conversely, a predicate constant on fibres is a type. -/
theorem isType_of_conv {P : Tm → Prop} (h : ∀ t u, Conv t u → (P t ↔ P u)) : IsType P :=
  fun t u st => h t u (Relation.EqvGen.rel _ _ ⟨st⟩)

/-- **Closing** a predicate (the essay's "Close it"): everything in a fibre that meets it. -/
def close (P : Tm → Prop) : Tm → Prop := fun t => ∃ u, P u ∧ Conv t u

theorem le_close (P : Tm → Prop) (t : Tm) (h : P t) : close P t :=
  ⟨t, h, Relation.EqvGen.refl _⟩

theorem isType_close (P : Tm → Prop) : IsType (close P) := by
  intro t u st
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨st⟩)) h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨st⟩) h⟩

/-- The closure is the least type containing the predicate. -/
theorem close_le {P Q : Tm → Prop} (hQ : IsType Q) (h : ∀ t, P t → Q t) (t : Tm)
    (ht : close P t) : Q t := by
  obtain ⟨u, hu, hc⟩ := ht
  exact (hQ.conv hc).2 (h u hu)

/-- The predicate defined by a probe: applying the term to any member of `A` gives a member
of `B`. This is `⟦A → B⟧`. -/
def Arr (A B : Tm → Prop) : Tm → Prop := fun t => ∀ u, A u → B (t ⬝ u)

/-- A predicate defined by a probe is a type as soon as its result predicate is. -/
theorem isType_arr {A B : Tm → Prop} (hB : IsType B) : IsType (Arr A B) := by
  intro t t' st
  exact forall₂_congr fun u _ => hB (Step.appL u st)

/-- **Fundamental lemma for K** (the essay's figure): `K ∈ ⟦A → B → A⟧` for any type `A`. -/
theorem fundamental_K {A B : Tm → Prop} (hA : IsType A) : Arr A (Arr B A) .K := by
  intro u hu v _
  exact (hA (Step.k u v)).2 hu

/-- **Fundamental lemma for I.** -/
theorem fundamental_I {A : Tm → Prop} (hA : IsType A) : Arr A A .I :=
  fun u hu => (hA (Step.i u)).2 hu

/-- **Fundamental lemma for S.** Only the result type needs to be a type. -/
theorem fundamental_S {A B C : Tm → Prop} (hC : IsType C) :
    Arr (Arr A (Arr B C)) (Arr (Arr A B) (Arr A C)) .S := by
  intro x hx y hy z hz
  exact (hC (Step.s x y z)).2 (hx z hz (y ⬝ z) (hy z hz))

/-- The rule `S K y → I` is sound: `S K y x` runs to `x`, whatever `y` is. -/
def skRun (y x : Tm) : Red (.S ⬝ .K ⬝ y ⬝ x) x :=
  r2 (Step.s .K y x) (Step.k x (y ⬝ x))

/-- The two runs of `K a (I b)` to `a` (discard `I b` at once, or run it first) are counted
as one run: they differ by an elementary square. -/
theorem kaib_one_run (a b : Tm) :
    PermEq (r2 (Step.appR (.K ⬝ a) (Step.i b)) (Step.k a b)) (r1 (Step.k a (.I ⬝ b))) :=
  Relation.EqvGen.rel _ _ (Sq.k_nat₂ a (Step.i b))

/-- The loop of `ω ω` in the order the essay draws it: the S-step, then the I-step in
argument position, then the I-step in function position. -/
def omegaLoop' : Red Ω Ω :=
  r3 (Step.s .I .I sii) (Step.appR (.I ⬝ sii) (Step.i sii)) (Step.appL sii (Step.i sii))

theorem omegaLoop'_wt : Red.wt omegaLoop' = 1 := by
  simp [omegaLoop', r3, r2, r1, Red.wt, Step.wt]

/-- The two orders of the loop differ by one square of disjoint redexes. -/
theorem omegaLoop_permEq : PermEq omegaLoop omegaLoop' := by
  have e := Sq.whisker (r1 (Step.s .I .I sii)) .nil (Sq.disjoint (Step.i sii) (Step.i sii))
  simp only [Quiver.Path.comp_cons, Quiver.Path.comp_nil, Quiver.Path.nil_comp, r1, r2] at e
  simp only [omegaLoop, omegaLoop', r3, r2, r1]
  exact Relation.EqvGen.rel _ _ e

/-- The loop as drawn is absorbed by no continuation. -/
theorem not_absorbed' {u : Tm} (h : Red Ω u) : ¬ PermEq (omegaLoop'.comp h) h := by
  intro hp
  have := wt_permEq kfree_Ω hp
  rw [Red.wt_comp, omegaLoop'_wt] at this
  omega

end FormalComputation.SKI
