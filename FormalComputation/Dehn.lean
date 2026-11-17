import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Nat.Lattice

/-!
# Cost equals area (PROOF_MAP G1–G3)

For a group presentation `⟨X | R⟩`, a step deletes a relator (or its inverse) from anywhere
in a free-group element, at cost 1. Free reduction costs nothing because objects are
free-group elements. The least number of steps from `w` to `1` is the area of `w`: the
least number of conjugates of relators whose product is `w`. Key identity:
`u * r * v = (u * r * u⁻¹) * (u * v)`.
-/

namespace FormalComputation.Dehn

variable {X : Type*} (R : Set (FreeGroup X))

/-- **G1.** Relators and their inverses. -/
def Rsym : Set (FreeGroup X) := R ∪ {r | r⁻¹ ∈ R}

/-- **G1.** One step: delete a relator or inverse relator. -/
inductive DStep : FreeGroup X → FreeGroup X → Prop
  | del (u r v : FreeGroup X) (hr : r ∈ Rsym R) : DStep (u * r * v) (u * v)

/-- **G1.** Chains of exactly `n` steps. -/
inductive DChain : ℕ → FreeGroup X → FreeGroup X → Prop
  | nil (g : FreeGroup X) : DChain 0 g g
  | cons {n : ℕ} {g h k : FreeGroup X} : DStep R g h → DChain n h k → DChain (n + 1) g k

/-- **G2.** `w` is a product of `n` conjugates of relators or their inverses. -/
def IsProdConj (n : ℕ) (w : FreeGroup X) : Prop :=
  ∃ l : List (FreeGroup X × FreeGroup X), l.length = n ∧
    (∀ p ∈ l, p.2 ∈ Rsym R) ∧
    w = (l.map fun p => p.1 * p.2 * p.1⁻¹).prod

/-- **G3.** `n` deletions take `w` to `1` exactly when `w` is a product of `n` conjugates. -/
theorem dchain_iff_prodConj (n : ℕ) (w : FreeGroup X) :
    DChain R n w 1 ↔ IsProdConj R n w := by
  sorry

/-- **G3.** Minimal trace cost equals area. -/
theorem cost_eq_area (w : FreeGroup X) :
    sInf {n | DChain R n w 1} = sInf {n | IsProdConj R n w} := by
  sorry

end FormalComputation.Dehn
