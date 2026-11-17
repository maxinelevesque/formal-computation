import FormalComputation.Presentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Traces (PROOF_MAP D6, tier stretch)

A trace is a cell decomposition: built from identities, pushouts of steps, and composition.
Small-step evaluation is a trace of the big step `X ⟶ LX`.
-/

universe v u

namespace FormalComputation

open CategoryTheory Limits

variable {P : Type u} [Category.{v} P]

/-- **D6.** Cell decompositions of a map. -/
inductive Trace (𝔓 : Presentation P) : {X Y : P} → (X ⟶ Y) → Type (max u v)
  | id (X : P) : Trace 𝔓 (𝟙 X)
  | cell {A B X Y : P} (s : A ⟶ B) (hs : 𝔓.steps s) (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y)
      (sq : IsPushout s a b f) : Trace 𝔓 f
  | comp {X Y Z : P} {f : X ⟶ Y} {g : Y ⟶ Z} : Trace 𝔓 f → Trace 𝔓 g → Trace 𝔓 (f ≫ g)

namespace Trace

variable {𝔓 : Presentation P}

/-- **D6.** The number of cells. -/
def length : {X Y : P} → {f : X ⟶ Y} → Trace 𝔓 f → ℕ
  | _, _, _, .id _ => 0
  | _, _, _, .cell .. => 1
  | _, _, _, .comp t t' => t.length + t'.length

/-- **D6.** A map with a trace is a computation. -/
theorem mem_E {X Y : P} {f : X ⟶ Y} (t : Trace 𝔓 f) : 𝔓.E f := by
  sorry

end Trace

end FormalComputation
