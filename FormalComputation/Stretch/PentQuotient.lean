import FormalComputation.Pentagon

/-!
# Imposing the pentagon (PROOF_MAP P3, stretch part)

The free reduction category on the pentagon, modulo `top = bot`, is the Tamari poset.
-/

namespace FormalComputation.Pentagon

open CategoryTheory

/-- The pentagon equation. -/
inductive PentRel : HomRel PentCat
  | pent : PentRel top bot

/-- **P3 (stretch).** The quotient by the pentagon equation is the Tamari poset. -/
noncomputable def pentQuotientEquiv : CategoryTheory.Quotient PentRel ≌ Tamari4 :=
  sorry

end FormalComputation.Pentagon
