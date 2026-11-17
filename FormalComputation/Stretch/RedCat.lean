import FormalComputation.SKI.PermEq
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# The K-free reduction category (PROOF_MAP K9, tier stretch)

Reductions between K-free terms modulo permutation equivalence form a category. The weight
is a functor from it to the one-object groupoid on `ℤ`, so the loop at `Ω` has infinite
order in the reduction groupoid.
-/

namespace FormalComputation.SKI

open CategoryTheory

/-- Permutation equivalence is compatible with composition. -/
theorem PermEq.comp_congr {t u v : Tm} {p p' : Red t u} {q q' : Red u v} :
    PermEq p p' → PermEq q q' → PermEq (p.comp q) (p'.comp q') := by
  sorry

/-- **K9.** K-free terms. -/
def RedCat : Type := { t : Tm // KFree t }

/-- **K9.** Reductions modulo permutation equivalence. -/
instance : Category RedCat :=
  sorry

/-- **K9.** The weight as a functor to `ℤ`. -/
def wtFunctor : RedCat ⥤ SingleObj (Multiplicative ℤ) :=
  sorry

/-- `Ω` as an object of the K-free reduction category. -/
def ΩObj : RedCat := ⟨Ω, kfree_Ω⟩

/-- **K9.** The loop at `Ω` has infinite order in the reduction groupoid. -/
theorem omegaLoop_infinite_order (loop : ΩObj ⟶ ΩObj)
    (hloop : wtFunctor.map loop = Multiplicative.ofAdd (1 : ℤ)) (m n : ℕ)
    (h : (⊤ : MorphismProperty RedCat).Q.map ((loop : End ΩObj) ^ m) =
      (⊤ : MorphismProperty RedCat).Q.map ((loop : End ΩObj) ^ n)) : m = n := by
  sorry

end FormalComputation.SKI
