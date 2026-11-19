import FormalComputation.Predicates

/-!
# Observation as a pairing (`notes/12-observation.md`)

Decision of 2026-11-19: an **observation** is a pairing between descriptions and observers,
and observers given by families are a special case.

* `Pairing D O`: which observers accept which descriptions.
* `Pairing.orth T` (written `T^⊥`): the descriptions that every observer in `T` accepts.
* `Pairing.Same`: sameness under the observation, agreement on every observer.
* `Pairing.Invariant`: no step changes any verdict. For an invariant observation every
  `T^⊥` is a type (`orth_invariant`), so the only proof of invariance needed is for the
  pairing, once.
* `Lens π π'`: descriptions go forward (`get`), observers go back (`put`), and an observer
  sent back sees exactly what it sees forward. (This is a morphism of Chu spaces.)
  Lenses compose, carry sameness forward (`Lens.same`), and pull types back to types:
  `get⁻¹(T^⊥) = (put T)^⊥` (`Lens.preimage_orth`). Types built by composing lenses are
  therefore types with no further work.
* Families as observers (`familyPairing`): a class of predicate families over a dynamic
  presentation, with `B` accepting `t` when `B t` is inhabited. If the families are
  behaviours, the pairing is invariant (`familyPairing_invariant`), by the
  characterization of predicates as behaviours.
-/

universe v u

namespace FormalComputation.Obs

open CategoryTheory

/-- An **observation**: which observers accept which descriptions. -/
structure Pairing (D : Type*) (O : Type*) where
  pass : D → O → Prop

variable {D O D' O' D'' O'' : Type*}

namespace Pairing

variable (π : Pairing D O)

/-- `T^⊥`: the descriptions that every observer in `T` accepts. -/
def orth (T : Set O) : Set D := {d | ∀ o ∈ T, π.pass d o}

theorem mem_orth {T : Set O} {d : D} : d ∈ π.orth T ↔ ∀ o ∈ T, π.pass d o := Iff.rfl

/-- **Sameness under the observation**: every observer gives the same verdict. -/
def Same (d e : D) : Prop := ∀ o, π.pass d o ↔ π.pass e o

/-- The observation is **invariant** along `step` when no step changes a verdict. -/
def Invariant (step : D → D → Prop) : Prop :=
  ∀ ⦃d e : D⦄, step d e → ∀ o, (π.pass d o ↔ π.pass e o)

/-- A set `T^⊥` cannot separate descriptions that the observation does not separate. -/
theorem orth_respects (T : Set O) {d e : D} (h : π.Same d e) : d ∈ π.orth T ↔ e ∈ π.orth T := by
  rw [mem_orth, mem_orth]
  exact forall₂_congr fun o _ => h o

/-- **For an invariant observation, every `T^⊥` is a type**: no step changes membership. -/
theorem orth_invariant {step : D → D → Prop} (hπ : π.Invariant step) (T : Set O) ⦃d e : D⦄
    (h : step d e) : d ∈ π.orth T ↔ e ∈ π.orth T := by
  rw [mem_orth, mem_orth]
  exact forall₂_congr fun o _ => hπ h o

/-- More observers, fewer descriptions: `(⋃ Tᵢ)^⊥ = ⋂ Tᵢ^⊥`. -/
theorem orth_iUnion {ι : Sort*} (T : ι → Set O) : π.orth (⋃ i, T i) = ⋂ i, π.orth (T i) := by
  ext d
  rw [Set.mem_iInter, mem_orth]
  constructor
  · intro h i
    rw [mem_orth]
    intro o ho
    exact h o (Set.mem_iUnion.2 ⟨i, ho⟩)
  · intro h o ho
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ho
    exact (mem_orth π).1 (h i) o hi

end Pairing

/-- A **lens** from `π` to `π'`: descriptions go forward by `get`, observers go back by
`put`, and an observer sent back sees exactly what it sees forward. -/
structure Lens (π : Pairing D O) (π' : Pairing D' O') where
  get : D → D'
  put : O' → O
  pass_put : ∀ d o', π.pass d (put o') ↔ π'.pass (get d) o'

namespace Lens

variable {π : Pairing D O} {π' : Pairing D' O'} {π'' : Pairing D'' O''}

/-- The identity lens. -/
def id (π : Pairing D O) : Lens π π := ⟨fun d => d, fun o => o, fun _ _ => Iff.rfl⟩

/-- **Lenses compose.** -/
def comp (ℓ : Lens π π') (m : Lens π' π'') : Lens π π'' where
  get d := m.get (ℓ.get d)
  put o := ℓ.put (m.put o)
  pass_put d o := (ℓ.pass_put d (m.put o)).trans (m.pass_put (ℓ.get d) o)

/-- **A lens pulls types back to types**: `get⁻¹(T^⊥) = (put T)^⊥`. -/
theorem preimage_orth (ℓ : Lens π π') (T : Set O') :
    ℓ.get ⁻¹' π'.orth T = π.orth (ℓ.put '' T) := by
  ext d
  rw [Set.mem_preimage, Pairing.mem_orth, Pairing.mem_orth]
  constructor
  · rintro h _ ⟨o, ho, rfl⟩
    exact (ℓ.pass_put d o).2 (h o ho)
  · intro h o ho
    exact (ℓ.pass_put d o).1 (h _ (Set.mem_image_of_mem ℓ.put ho))

/-- **A lens carries sameness forward.** When the lenses are contexts, this says that sameness
under the observation is a congruence. -/
theorem same (ℓ : Lens π π') {d e : D} (h : π.Same d e) : π'.Same (ℓ.get d) (ℓ.get e) :=
  fun o => (ℓ.pass_put d o).symm.trans ((h (ℓ.put o)).trans (ℓ.pass_put e o))

end Lens

/-! ### Families as observers -/

section Families

variable {A : Type u} [Category.{v} A]

/-- **Families as observers.** A class `𝒪` of covariant families gives a pairing: `B` accepts
`t` when `B t` is inhabited. -/
def familyPairing (𝒪 : Set (A ⥤ Type v)) : Pairing A 𝒪 where
  pass t B := Nonempty (B.1.obj t)

/-- If the observers are predicates (subsingleton-valued) and behaviours, the family pairing
is invariant along steps: a step changes no verdict. -/
theorem familyPairing_invariant (𝒜 : DynPresentation A) (𝒪 : Set (A ⥤ Type v))
    (hsub : ∀ B ∈ 𝒪, ∀ t, Subsingleton (B.obj t))
    (hbeh : ∀ B ∈ 𝒪, 𝒜.toCopresentation.Beh B) :
    (familyPairing 𝒪).Invariant (fun t t' => ∃ s : t ⟶ t', 𝒜.steps s) := by
  intro t t' h o
  obtain ⟨s, hs⟩ := h
  obtain ⟨B, hB⟩ := o
  haveI := hsub B hB
  exact (beh_iff_of_subsingleton_co 𝒜 B).1 (hbeh B hB) s hs

end Families

end FormalComputation.Obs
