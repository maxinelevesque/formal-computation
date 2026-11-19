import FormalComputation.Observation

/-!
# Calculi with probes, in general

The SKI results of the essay "Atoms and Probes" use only a few facts about combinatory logic:
- a one-step relation;
- contexts with any number of holes, which can be plugged and composed;
- steps that survive being put in a context;
- outcomes that a probe may read, and that do not step;
- confluence.

This file states the essay's results for any calculus with those ingredients (`Calculus`), so
that SKI, tree calculus and other calculi are instances.

Proved here for every calculus:
- **Three equalities, each coarser than the one before.** Sameness of text implies sameness
  after running, and, given confluence, sameness after running implies sameness under every
  probe (`probeEq_of_conv`).
- **Sameness under probes is a congruence** (`probeEq_plug`), as an instance of lenses
  carrying sameness forward (`ctxLens`, `Obs.Lens.same`).
- **The probes form an invariant pairing** (`probes_invariant`, given confluence), so every
  set of terms defined by probe tests is a type (`isType_orth`), and contexts are lenses that
  pull such types back to types.
- **Probes that read code see what running sees** on terms that have a value
  (`codeEq_iff_conv`).
-/

namespace FormalComputation

open Relation Obs

/-- A **calculus with probes**.
- `Step`: one step of running.
- `Ctx`: probes, meaning contexts with any number of holes. `plug C t` puts `t` in every hole
  of `C`. `subst C D` puts `D` in every hole of `C`. `hole` is the probe that is just a hole.
- `reds_plug`: a step inside a context is a run of the plugged term.
- `Out`: the outcomes a probe may read. They do not step. -/
structure Calculus where
  Tm : Type
  Step : Tm → Tm → Prop
  Ctx : Type
  hole : Ctx
  plug : Ctx → Tm → Tm
  subst : Ctx → Ctx → Ctx
  plug_hole : ∀ t, plug hole t = t
  plug_subst : ∀ C D t, plug (subst C D) t = plug C (plug D t)
  reds_plug : ∀ C {t u}, Step t u → ReflTransGen Step (plug C t) (plug C u)
  Out : Tm → Prop
  out_normal : ∀ {r u}, Out r → ¬ Step r u

namespace Calculus

variable (L : Calculus)

/-- Running: any number of steps. -/
abbrev Reds : L.Tm → L.Tm → Prop := ReflTransGen L.Step

/-- **Sameness after running**: one fibre, steps taken either way. -/
def Conv : L.Tm → L.Tm → Prop := EqvGen L.Step

/-- A term that takes no step. -/
def IsNormal (t : L.Tm) : Prop := ∀ u, ¬ L.Step t u

/-- **Confluence**: two runs from one term can be continued until they meet. -/
def Confluent : Prop :=
  ∀ ⦃a b c : L.Tm⦄, L.Reds a b → L.Reds a c → ∃ d, L.Reds b d ∧ L.Reds c d

/-- The probe reads `r` from `t`: `t` runs to `r`, and `r` is an outcome. -/
def Reads (t r : L.Tm) : Prop := L.Reds t r ∧ L.Out r

/-- **Sameness under every probe.** -/
def ProbeEq (t u : L.Tm) : Prop :=
  ∀ (C : L.Ctx) (r : L.Tm), L.Reads (L.plug C t) r ↔ L.Reads (L.plug C u) r

/-- A **type**: a predicate that no step changes. -/
def IsType (P : L.Tm → Prop) : Prop := ∀ ⦃t u : L.Tm⦄, L.Step t u → (P t ↔ P u)

variable {L}

theorem reds_conv {t u : L.Tm} (h : L.Reds t u) : L.Conv t u := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ s ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ s)

theorem reds_plug' (C : L.Ctx) {t u : L.Tm} (h : L.Reds t u) :
    L.Reds (L.plug C t) (L.plug C u) := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.trans (L.reds_plug C s)

theorem conv_plug (C : L.Ctx) {t u : L.Tm} (h : L.Conv t u) :
    L.Conv (L.plug C t) (L.plug C u) := by
  induction h with
  | rel x y s => exact reds_conv (L.reds_plug C s)
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

/-- A type takes one value on each fibre. -/
theorem IsType.conv {P : L.Tm → Prop} (hP : L.IsType P) {t u : L.Tm} (h : L.Conv t u) :
    P t ↔ P u := by
  induction h with
  | rel x y s => exact hP s
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem reds_normal {t u : L.Tm} (ht : L.IsNormal t) (h : L.Reds t u) : u = t := by
  rcases ReflTransGen.cases_head h with rfl | ⟨c, s, _⟩
  · rfl
  · exact (ht c s).elim

section Confluent

variable (hc : L.Confluent)
include hc

/-- Terms in one fibre run to a common term. -/
theorem conv_join {t u : L.Tm} (h : L.Conv t u) : ∃ d, L.Reds t d ∧ L.Reds u d := by
  induction h with
  | rel x y s => exact ⟨y, .single s, .refl⟩
  | refl x => exact ⟨x, .refl, .refl⟩
  | symm x y _ ih =>
    obtain ⟨d, h₁, h₂⟩ := ih
    exact ⟨d, h₂, h₁⟩
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨d₁, a₁, b₁⟩ := ih₁
    obtain ⟨d₂, a₂, b₂⟩ := ih₂
    obtain ⟨e, c₁, c₂⟩ := hc b₁ a₂
    exact ⟨e, a₁.trans c₁, b₂.trans c₂⟩

/-- **Two different normal forms never lie in one fibre.** -/
theorem conv_normal_eq {t u : L.Tm} (h : L.Conv t u) (ht : L.IsNormal t) (hu : L.IsNormal u) :
    t = u := by
  obtain ⟨d, a, b⟩ := conv_join hc h
  rw [← reds_normal ht a, ← reds_normal hu b]

/-- A term in the fibre of a normal form runs to it. -/
theorem reds_of_conv_normal {u r : L.Tm} (h : L.Conv u r) (hr : L.IsNormal r) :
    L.Reds u r := by
  obtain ⟨d, a, b⟩ := conv_join hc h
  rw [reds_normal hr b] at a
  exact a

theorem isNormal_of_out {r : L.Tm} (hr : L.Out r) : L.IsNormal r :=
  fun _ s => L.out_normal hr s

theorem reads_of_conv {a b r : L.Tm} (h : L.Conv a b) (hr : L.Reads a r) : L.Reads b r :=
  ⟨reds_of_conv_normal hc (EqvGen.trans _ _ _ (EqvGen.symm _ _ h) (reds_conv hr.1))
    (isNormal_of_out hc hr.2), hr.2⟩

/-- **Sameness after running implies sameness under probes.** The proof uses confluence. -/
theorem probeEq_of_conv {t u : L.Tm} (h : L.Conv t u) : L.ProbeEq t u := fun C _ =>
  ⟨reads_of_conv hc (conv_plug C h), reads_of_conv hc (EqvGen.symm _ _ (conv_plug C h))⟩

/-- A probe reads at most one outcome. -/
theorem reads_unique {t r r' : L.Tm} (h : L.Reads t r) (h' : L.Reads t r') : r = r' :=
  conv_normal_eq hc (EqvGen.trans _ _ _ (EqvGen.symm _ _ (reds_conv h.1)) (reds_conv h'.1))
    (isNormal_of_out hc h.2) (isNormal_of_out hc h'.2)

end Confluent

/-- Sameness of text implies sameness after running: the first link in the chain. -/
theorem conv_of_eq {t u : L.Tm} (h : t = u) : L.Conv t u := by
  subst h
  exact EqvGen.refl _

/-! ### The probes as a pairing; contexts as lenses -/

variable (L) in
/-- **The probes as a pairing**: an observer is a probe with the outcome it expects. -/
def probes : Pairing L.Tm (L.Ctx × L.Tm) where
  pass t o := L.Reads (L.plug o.1 t) o.2

theorem probes_same_iff {t u : L.Tm} : L.probes.Same t u ↔ L.ProbeEq t u :=
  ⟨fun h C r => h (C, r), fun h o => h o.1 o.2⟩

variable (L) in
/-- **Every context is a lens.** Forward, `t` goes to `D[t]`. Back, a probe `C` goes to
`C[D]`. -/
def ctxLens (D : L.Ctx) : Lens L.probes L.probes where
  get t := L.plug D t
  put o := (L.subst o.1 D, o.2)
  pass_put t o := Iff.of_eq (congrArg (fun s => L.Reads s o.2) (L.plug_subst o.1 D t))

/-- **Sameness under probes is a congruence**: the lens of a context carries it forward. -/
theorem probeEq_plug {t u : L.Tm} (h : L.ProbeEq t u) (D : L.Ctx) :
    L.ProbeEq (L.plug D t) (L.plug D u) :=
  probes_same_iff.1 ((L.ctxLens D).same (probes_same_iff.2 h))

/-- **The probes form an invariant pairing**, given confluence: no step changes a reading. -/
theorem probes_invariant (hc : L.Confluent) : L.probes.Invariant L.Step := by
  intro t u s o
  exact probeEq_of_conv hc (EqvGen.rel _ _ s) o.1 o.2

/-- **Every set of terms defined by probe tests is a type**, given confluence. -/
theorem isType_orth (hc : L.Confluent) (T : Set (L.Ctx × L.Tm)) :
    L.IsType (· ∈ L.probes.orth T) := by
  intro t u s
  exact L.probes.orth_invariant (probes_invariant hc) T s

/-! ### Probes that read code -/

/-- A probe that may **read code** reads any normal form the run reaches. -/
def ReadsCode (t r : L.Tm) : Prop := L.Reds t r ∧ L.IsNormal r

/-- Sameness under probes that read code. -/
def CodeEq (t u : L.Tm) : Prop :=
  ∀ (C : L.Ctx) (r : L.Tm), L.ReadsCode (L.plug C t) r ↔ L.ReadsCode (L.plug C u) r

theorem readsCode_of_conv (hc : L.Confluent) {a b r : L.Tm} (h : L.Conv a b)
    (hr : L.ReadsCode a r) : L.ReadsCode b r :=
  ⟨reds_of_conv_normal hc (EqvGen.trans _ _ _ (EqvGen.symm _ _ h) (reds_conv hr.1)) hr.2, hr.2⟩

/-- **Probes that read code see exactly what running sees**, on terms that have a value. -/
theorem codeEq_iff_conv (hc : L.Confluent) {t u : L.Tm} (ht : ∃ r, L.ReadsCode t r) :
    L.CodeEq t u ↔ L.Conv t u := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := ht
    have hr' : L.ReadsCode (L.plug L.hole t) r := by rw [L.plug_hole]; exact hr
    have hu := (h L.hole r).1 hr'
    rw [L.plug_hole] at hu
    exact EqvGen.trans _ _ _ (reds_conv hr.1) (EqvGen.symm _ _ (reds_conv hu.1))
  · intro h C _
    exact ⟨readsCode_of_conv hc (conv_plug C h),
      readsCode_of_conv hc (EqvGen.symm _ _ (conv_plug C h))⟩

end Calculus

end FormalComputation
