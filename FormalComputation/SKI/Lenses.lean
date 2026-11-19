import FormalComputation.SKI.Probes
import FormalComputation.Observation

/-!
# SKI: the essay's probes as a pairing, and types built from lenses

The essay's observation is the pairing `probes`: an observer is a probe with the outcome it
expects, and it accepts `t` when it reads that outcome from `t`.

* Sameness under this pairing is sameness under every probe (`probes_same_iff`).
* The pairing is invariant along steps (`probes_invariant`), by confluence. So every set of
  terms of the form `T^⊥`, the terms passing a set `T` of probe tests, is a type
  (`isType_orth`), and a probe type is the case of one test (`probePred_iff_mem_orth`).
* **Lenses.** "Apply to `a`" is a lens (`applyTo`): forward a term `t` goes to `t a`, and back a
  probe `C` goes to `C[[ ] a]`. Composites of lenses are lenses, so types built by composing
  them need no proof of invariance of their own.
* **Arrow types are built from lenses** (`arr_iff_mem_orth`): if `B = T^⊥`, then `A → B` is the
  set of terms passing every test in `T` sent back along "apply to `a`", for every `a` in `A`.
-/

namespace FormalComputation.SKI

open Relation FormalComputation.Obs

/-- **The essay's observation as a pairing.** An observer is a probe with the outcome it
expects; it accepts `t` when it reads that outcome from `t`. -/
def probes : Pairing Tm (Probe × Tm) where
  pass t o := Reads (o.1.plug t) o.2

/-- Sameness under the pairing is sameness under every probe. -/
theorem probes_same_iff {t u : Tm} : probes.Same t u ↔ ProbeEq t u :=
  ⟨fun h C r => h (C, r), fun h o => h o.1 o.2⟩

/-- **The pairing is invariant along steps.** The proof uses confluence. -/
theorem probes_invariant : probes.Invariant (fun t u => Nonempty (Step t u)) := by
  intro t u h o
  exact probeEq_of_conv (EqvGen.rel _ _ h) o.1 o.2

/-- **Every set of terms defined by probe tests is a type.** -/
theorem isType_orth (T : Set (Probe × Tm)) : IsType (· ∈ probes.orth T) := by
  intro t u s
  exact probes.orth_invariant probes_invariant T ⟨s⟩

/-- A probe type is `T^⊥` for a single test. -/
theorem probePred_iff_mem_orth (C : Probe) (r t : Tm) :
    ProbePred C r t ↔ t ∈ probes.orth {(C, r)} := by
  rw [Pairing.mem_orth]
  constructor
  · intro h o ho
    rw [Set.mem_singleton_iff] at ho
    subst ho
    exact h
  · intro h
    exact h _ (Set.mem_singleton _)

/-- **The lens "apply to `a`".** Forward, a term `t` goes to `t a`. Back, a probe `C` goes to
`C[[ ] a]`, which puts `t a` where `C` put `t`. -/
def applyTo (a : Tm) : Lens probes probes where
  get t := t ⬝ a
  put o := (o.1.subst (.app .hole (.lit a)), o.2)
  pass_put t o :=
    Iff.of_eq (congrArg (fun s => Reads s o.2) (Probe.plug_subst o.1 (.app .hole (.lit a)) t))

/-- **Arrow types are built from lenses.** If `B = T^⊥`, then `A → B` is the set of terms
that pass every test of `T` sent back along "apply to `a`", for every `a` in `A`. -/
theorem arr_iff_mem_orth (A : Tm → Prop) (T : Set (Probe × Tm)) (t : Tm) :
    Arr A (· ∈ probes.orth T) t ↔
      t ∈ probes.orth (⋃ a : {a // A a}, (applyTo a.1).put '' T) := by
  have key : ∀ u, (t ⬝ u ∈ probes.orth T ↔ t ∈ probes.orth ((applyTo u).put '' T)) :=
    fun u => Set.ext_iff.1 ((applyTo u).preimage_orth T) t
  rw [probes.orth_iUnion, Set.mem_iInter]
  constructor
  · intro h a
    exact (key a.1).1 (h a.1 a.2)
  · intro h u hu
    exact (key u).2 (h ⟨u, hu⟩)

/-- The probe `[ ] x y` is the composite of two lenses, "apply to `x`" then "apply to `y`". -/
theorem applyTo_comp_get (x y t : Tm) :
    ((applyTo x).comp (applyTo y)).get t = t ⬝ x ⬝ y := rfl

end FormalComputation.SKI
