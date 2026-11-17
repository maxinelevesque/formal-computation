import FormalComputation.Translation

/-!
# Translations and conjoints (PROOF_MAP B7, tier stretch)

A translation is a functor on terms whose pushforward sends steps to computations. Its
pushforward is the left Kan extension, so the categories of terms are taken small here:
that is what makes the left Kan extension into `Type v` exist.
-/

universe v

namespace FormalComputation

open CategoryTheory Limits

variable {A A' : Type v} [SmallCategory A] [SmallCategory A']

/-- **B7.** A translation: a functor on terms whose pushforward sends steps to computations. -/
structure Translation (𝒜 : DynPresentation A) (𝒜' : DynPresentation A') where
  F : A ⥤ A'
  steps_to_E : ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s →
    𝒜'.toPresentation.E (coyoneda.map (F.map s).op)

namespace Translation

variable {𝒜 : DynPresentation A} {𝒜' : DynPresentation A'}

/-- **B7.** The companion: pushforward (left Kan extension along `F`) ⊣ restriction. -/
noncomputable def toSimulation (τ : Translation 𝒜 𝒜') :
    Simulation 𝒜.toPresentation 𝒜'.toPresentation :=
  sorry

/-- **B7.** `F` has a conjoint when restriction also sends steps to computations. -/
def HasConjoint (τ : Translation 𝒜 𝒜') : Prop :=
  ∀ ⦃X Y : A' ⥤ Type v⦄ (f : X ⟶ Y), 𝒜'.toPresentation.steps f →
    𝒜.toPresentation.E (((Functor.whiskeringLeft A A' (Type v)).obj τ.F).map f)

/-- **B7.** Then restriction on behaviours is also a left adjoint: an adjoint triple. -/
theorem onBeh_isLeftAdjoint_of_hasConjoint [Reflective 𝒜.toPresentation.Beh.ι]
    (τ : Translation 𝒜 𝒜') (h : τ.HasConjoint) :
    τ.toSimulation.onBeh.IsLeftAdjoint := by
  sorry

end Translation

end FormalComputation
