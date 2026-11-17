import FormalComputation.Presentation

/-!
# Theorem A: behaviours are local systems (PROOF_MAP A1–A4)

In the dynamic picture, a behaviour is a covariant family `B : A ⥤ Type v` on which every
step acts bijectively (A1). These are the functors inverting the steps (A2), hence the
functors out of the localization of `A` at the steps: local systems on the reduction
groupoid (A3). If `A` has a terminal object and every map is a step, the reduction
groupoid is a point and behaviours are bare sets (A4).
-/

universe w v u

namespace FormalComputation

open CategoryTheory Limits

variable {A : Type u} [Category.{v} A]

/-- **A1.** A family is local exactly when every step acts on it bijectively (Yoneda). -/
theorem beh_iff_map_bijective (𝒜 : DynPresentation A) (B : A ⥤ Type v) :
    𝒜.toPresentation.Beh B ↔
      ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s → Function.Bijective (B.map s) := by
  sorry

/-- **A2.** Behaviours are the functors inverting the steps. -/
noncomputable def behEquivInverting (𝒜 : DynPresentation A) :
    𝒜.toPresentation.Beh.FullSubcategory ≌ 𝒜.steps.FunctorsInverting (Type v) :=
  sorry

/-- **A3. Theorem A.** Behaviours are local systems on the reduction groupoid: functors
out of the localization of `A` at the steps. -/
noncomputable def behEquivLocalSystems (𝒜 : DynPresentation A) :
    𝒜.toPresentation.Beh.FullSubcategory ≌ (𝒜.steps.Localization ⥤ Type v) :=
  sorry

/-- **A4.** If `A` has a terminal object, inverting every map gives the point. -/
theorem localization_trivial_of_terminal (n : A) (hn : IsTerminal n) :
    Nonempty ((⊤ : MorphismProperty A).Localization ≌ Discrete PUnit.{w + 1}) := by
  sorry

/-- **A4.** So if every map is a step and `A` has a terminal object, behaviours are bare
sets: evaluation is path-independent. -/
theorem beh_equiv_type_of_terminal (𝒜 : DynPresentation A) (h : 𝒜.steps = ⊤)
    (n : A) (hn : IsTerminal n) :
    Nonempty (𝒜.toPresentation.Beh.FullSubcategory ≌ Type v) := by
  sorry

end FormalComputation
