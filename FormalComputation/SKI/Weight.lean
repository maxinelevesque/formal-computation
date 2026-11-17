import FormalComputation.SKI.Syntax

/-!
# SKI: the right-spine weight and the loop at Ω (PROOF_MAP K4, K7)

The weight of a step is 1 for an S-step whose redex is reached by argument moves only, and
0 otherwise. It is the 1-cocycle given by the model of the K-free 2-theory in the
one-object groupoid on `ℤ` (application `(g, h) ↦ h`, S-rule `1`, I-rule `0`).

The loop `Ω → Ω` has weight 1. That it is not absorbed by any continuation needs K6 and is
in `FormalComputation/SKI/PermEq.lean`.
-/

namespace FormalComputation.SKI

/-- **K4.** Weight of a step: count S-steps on the right spine. -/
def Step.wt : {t u : Tm} → Step t u → ℤ
  | _, _, .s .. => 1
  | _, _, .i .. => 0
  | _, _, .k .. => 0
  | _, _, .appL _ _ => 0
  | _, _, .appR _ st => Step.wt st

/-- **K4.** Weight of a reduction: the sum over its steps. -/
def Red.wt : {t u : Tm} → Red t u → ℤ
  | _, _, .nil => 0
  | _, _, .cons p s => Red.wt p + Step.wt s

/-- **K4.** The weight is additive. -/
theorem Red.wt_comp {t u v : Tm} (p : Red t u) (q : Red u v) :
    Red.wt (p.comp q) = Red.wt p + Red.wt q := by
  induction q with
  | nil => simp [Red.wt]
  | cons q s ih => simp [Red.wt, ih, add_assoc]

/-- A reduction in function position has weight 0. -/
theorem Red.wt_mapAppL (u : Tm) {t t' : Tm} (p : Red t t') :
    Red.wt (Red.mapAppL u p) = 0 := by
  induction p with
  | nil => rfl
  | cons p s ih => simp [Red.mapAppL, Red.wt, Step.wt, ih]

/-- A reduction in argument position keeps its weight. -/
theorem Red.wt_mapAppR (t : Tm) {u u' : Tm} (p : Red u u') :
    Red.wt (Red.mapAppR t p) = Red.wt p := by
  induction p with
  | nil => rfl
  | cons p s ih => simp [Red.mapAppR, Red.wt, Step.wt, ih]

/-- **K7.** `S I I`. -/
def sii : Tm := .S ⬝ .I ⬝ .I

/-- **K7.** `Ω = S I I (S I I)`. -/
def Ω : Tm := sii ⬝ sii

/-- **K7.** The loop: S-step at the root, then the I-step in function position, then the
I-step in argument position. -/
def omegaLoop : Red Ω Ω :=
  r3 (Step.s .I .I sii) (Step.appL (.I ⬝ sii) (Step.i sii)) (Step.appR sii (Step.i sii))

/-- **K7.** The loop has weight 1. -/
theorem omegaLoop_wt : Red.wt omegaLoop = 1 := by
  rfl

/-- **K7.** `Ω` is K-free. -/
theorem kfree_Ω : KFree Ω := by
  simp [Ω, sii, KFree]

end FormalComputation.SKI
