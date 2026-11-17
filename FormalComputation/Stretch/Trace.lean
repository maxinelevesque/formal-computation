import FormalComputation.Presentation

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
inductive Trace (𝒫 : Presentation P) : {X Y : P} → (X ⟶ Y) → Type (max u v)
  | id (X : P) : Trace 𝒫 (𝟙 X)
  | cell {A B X Y : P} (s : A ⟶ B) (hs : 𝒫.steps s) (a : A ⟶ X) (b : B ⟶ Y) (f : X ⟶ Y)
      (sq : IsPushout s a b f) : Trace 𝒫 f
  | comp {X Y Z : P} {f : X ⟶ Y} {g : Y ⟶ Z} : Trace 𝒫 f → Trace 𝒫 g → Trace 𝒫 (f ≫ g)

namespace Trace

variable {𝒫 : Presentation P}

/-- **D6.** The number of cells. -/
def length : {X Y : P} → {f : X ⟶ Y} → Trace 𝒫 f → ℕ
  | _, _, _, .id _ => 0
  | _, _, _, .cell .. => 1
  | _, _, _, .comp t t' => t.length + t'.length

/-- **D6.** A map with a trace is a computation. -/
theorem mem_E {X Y : P} {f : X ⟶ Y} (t : Trace 𝒫 f) : 𝒫.E f := by
  sorry

end Trace

end FormalComputation
