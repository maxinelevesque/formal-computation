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

/-- **G3 (→).** A chain of `n` deletions from `g` to `k` writes `g k⁻¹` as a product of `n`
conjugates, using `u r v = (u r u⁻¹)(u v)`. -/
theorem isProdConj_of_dchain {n : ℕ} {g k : FreeGroup X} (h : DChain R n g k) :
    IsProdConj R n (g * k⁻¹) := by
  induction h with
  | nil g => exact ⟨[], rfl, by simp, by simp⟩
  | cons hs _ ih =>
    obtain ⟨l, hl, hmem, hprod⟩ := ih
    cases hs with
    | del u r v hr =>
      refine ⟨(u, r) :: l, by simp [hl], ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hr
        · exact hmem p hp
      · rw [List.map_cons, List.prod_cons, ← hprod]
        simp [mul_assoc]

/-- **G3 (←).** A product of conjugates is deleted one conjugate at a time. -/
theorem dchain_of_isProdConj : ∀ (l : List (FreeGroup X × FreeGroup X)),
    (∀ p ∈ l, p.2 ∈ Rsym R) →
      DChain R l.length (l.map fun p => p.1 * p.2 * p.1⁻¹).prod 1
  | [], _ => by simpa using DChain.nil (R := R) (1 : FreeGroup X)
  | (u, r) :: l, hmem => by
    have ih := dchain_of_isProdConj l (fun p hp => hmem p (List.mem_cons_of_mem _ hp))
    have hr : r ∈ Rsym R := hmem (u, r) List.mem_cons_self
    have key : ∀ w' : FreeGroup X, DChain R l.length w' 1 →
        DChain R (l.length + 1) (u * r * u⁻¹ * w') 1 := by
      intro w' hw'
      have hs := DStep.del (R := R) u r (u⁻¹ * w') hr
      rw [mul_inv_cancel_left] at hs
      rw [show u * r * u⁻¹ * w' = u * r * (u⁻¹ * w') by simp only [mul_assoc]]
      exact DChain.cons hs hw'
    simp only [List.length_cons, List.map_cons, List.prod_cons]
    exact key _ ih

/-- **G3.** `n` deletions take `w` to `1` exactly when `w` is a product of `n` conjugates. -/
theorem dchain_iff_prodConj (n : ℕ) (w : FreeGroup X) :
    DChain R n w 1 ↔ IsProdConj R n w := by
  constructor
  · intro h
    simpa using isProdConj_of_dchain R h
  · rintro ⟨l, rfl, hmem, rfl⟩
    exact dchain_of_isProdConj R l hmem

/-- **G3.** Minimal trace cost equals area. -/
theorem cost_eq_area (w : FreeGroup X) :
    sInf {n | DChain R n w 1} = sInf {n | IsProdConj R n w} :=
  congrArg sInf (Set.ext fun n => dchain_iff_prodConj R n w)

end FormalComputation.Dehn
