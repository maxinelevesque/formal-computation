import FormalComputation.Translation
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Translations and conjoints (PROOF_MAP B7, tier stretch)

A translation is a functor on terms whose pushforward sends steps to computations. On
presheaves the pushforward is the left Kan extension along `F.op`, so the categories of
terms are taken small here: that is what makes the left Kan extension into `Type v` exist.
-/

universe v

namespace FormalComputation

open CategoryTheory Limits

variable {A A' : Type v} [SmallCategory A] [SmallCategory A']

/-- **B7.** A translation: a functor on terms whose pushforward sends steps to computations. -/
structure Translation (𝒜 : DynPresentation A) (𝒜' : DynPresentation A') where
  F : A ⥤ A'
  steps_to_E : ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s →
    𝒜'.toPresentation.E (yoneda.map (F.map s))

namespace Translation

variable {𝒜 : DynPresentation A} {𝒜' : DynPresentation A'}

/-- **B7.** The companion: pushforward (left Kan extension along `F.op`) ⊣ restriction. -/
noncomputable def toSimulation (τ : Translation 𝒜 𝒜') :
    Simulation 𝒜.toPresentation 𝒜'.toPresentation :=
  sorry

/-- **B7.** `F` has a conjoint when restriction also sends steps to computations. -/
def HasConjoint (τ : Translation 𝒜 𝒜') : Prop :=
  ∀ ⦃X Y : A'ᵒᵖ ⥤ Type v⦄ (f : X ⟶ Y), 𝒜'.toPresentation.steps f →
    𝒜.toPresentation.E (((Functor.whiskeringLeft Aᵒᵖ A'ᵒᵖ (Type v)).obj τ.F.op).map f)

/-- **B7.** Then restriction on behaviours is also a left adjoint: an adjoint triple. -/
theorem onBeh_isLeftAdjoint_of_hasConjoint [Reflective 𝒜.toPresentation.Beh.ι]
    (τ : Translation 𝒜 𝒜') (h : τ.HasConjoint) :
    τ.toSimulation.onBeh.IsLeftAdjoint := by
  sorry

end Translation

end FormalComputation
