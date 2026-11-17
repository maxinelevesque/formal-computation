import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Logic.Relation
import Mathlib.Data.Int.Init

/-!
# SKI: terms and steps (PROOF_MAP K1–K3)

Steps are proof-relevant: `Step t u` is a type, so the two different reductions of
`I (I x)` to `I x` are different steps (K3).
-/

namespace FormalComputation.SKI

/-- **K1.** SKI terms. -/
inductive Tm
  | S
  | K
  | I
  | app : Tm → Tm → Tm
  deriving DecidableEq

@[inherit_doc] scoped infixl:70 " ⬝ " => Tm.app

/-- **K1.** Terms not containing `K`. -/
def KFree : Tm → Prop
  | .K => False
  | .S => True
  | .I => True
  | .app t u => KFree t ∧ KFree u

/-- **K2.** One-step reductions, as data. -/
inductive Step : Tm → Tm → Type
  | i (x : Tm) : Step (.I ⬝ x) x
  | k (x y : Tm) : Step (.K ⬝ x ⬝ y) x
  | s (x y z : Tm) : Step (.S ⬝ x ⬝ y ⬝ z) (x ⬝ z ⬝ (y ⬝ z))
  | appL {t t' : Tm} (u : Tm) : Step t t' → Step (t ⬝ u) (t' ⬝ u)
  | appR (t : Tm) {u u' : Tm} : Step u u' → Step (t ⬝ u) (t ⬝ u')

instance : Quiver Tm := ⟨Step⟩

/-- **K2.** Reductions: paths of steps. -/
abbrev Red (t u : Tm) := Quiver.Path t u

/-- **K2.** A step leaves the K-free fragment invariant. -/
theorem kfree_of_step {t u : Tm} : KFree t → Step t u → KFree u := by
  sorry

/-- **K3.** `I (I x)` reduces to `I x` in two different ways. -/
theorem accident_SKI (x : Tm) : Step.i (.I ⬝ x) ≠ Step.appR .I (Step.i x) := by
  sorry

/-! Paths built from listed steps (`⟦…⟧` in PROOF_MAP). -/

/-- A one-step reduction. -/
abbrev r1 {t u : Tm} (a : Step t u) : Red t u := Quiver.Path.nil.cons a

/-- A two-step reduction. -/
abbrev r2 {t u v : Tm} (a : Step t u) (b : Step u v) : Red t v := (r1 a).cons b

/-- A three-step reduction. -/
abbrev r3 {t u v w : Tm} (a : Step t u) (b : Step u v) (c : Step v w) : Red t w :=
  (r2 a b).cons c

/-- Apply a reduction in the function position, to every step. -/
def Red.mapAppL (u : Tm) : {t t' : Tm} → Red t t' → Red (t ⬝ u) (t' ⬝ u)
  | _, _, .nil => .nil
  | _, _, .cons p s => (Red.mapAppL u p).cons (Step.appL u s)

/-- Apply a reduction in the argument position, to every step. -/
def Red.mapAppR (t : Tm) : {u u' : Tm} → Red u u' → Red (t ⬝ u) (t ⬝ u')
  | _, _, .nil => .nil
  | _, _, .cons p s => (Red.mapAppR t p).cons (Step.appR t s)

end FormalComputation.SKI
