import FormalComputation.Orth
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-!
# Presentations (PROOF_MAP D1–D5)

A presentation is a category `P` of descriptions with a class of steps. Everything else is
derived: `M` (unique right lifting against steps), `E` (unique left lifting against `M`,
the computations), behaviours (the step-local objects), and conversions (the maps every
behaviour sees as an isomorphism).

D6 (traces) is tier "stretch" and lives in `FormalComputation/Stretch/Trace.lean`.
-/

universe v u

namespace FormalComputation

open CategoryTheory Limits

/-- **D1.** A presentation: a category of descriptions and a class of steps. -/
structure Presentation (P : Type u) [Category.{v} P] where
  steps : MorphismProperty P

namespace Presentation

variable {P : Type u} [Category.{v} P] (𝔓 : Presentation P)

/-- **D2.** Maps with unique right lifting against the steps. -/
def M : MorphismProperty P := rOrth 𝔓.steps

/-- **D2.** Computations: maps with unique left lifting against `M`. -/
def E : MorphismProperty P := lOrth 𝔓.M

/-- **D2.** Behaviours: the step-local objects. -/
def Beh : ObjectProperty P := 𝔓.steps.isLocal

/-- **D2.** Conversions: maps that every behaviour sees as an isomorphism. -/
def Conv : MorphismProperty P := 𝔓.Beh.isLocal

/-- **D3.** Every step is a computation. -/
theorem steps_le_E : 𝔓.steps ≤ 𝔓.E := by
  sorry

/-- **D3.** Every computation is a conversion. -/
theorem E_le_Conv [HasTerminal P] : 𝔓.E ≤ 𝔓.Conv := by
  sorry

/-- **D3.** Behaviours are the objects whose map to `⊤` is in `M`. -/
theorem beh_iff_M [HasTerminal P] (X : P) : 𝔓.Beh X ↔ 𝔓.M (terminal.from X) := by
  sorry

/-- **D3.** Conversions satisfy 2-out-of-3. -/
instance : 𝔓.Conv.HasTwoOutOfThreeProperty := by
  sorry

/-- **D4.** The size condition: `(E, M)` factors every map. -/
class Convergent : Prop where
  fac : 𝔓.E.HasFactorization 𝔓.M

/-- **D4 (added).** What convergence buys: with a terminal object, it makes behaviours
reflective, i.e. every description has a denotation. Factor `X ⟶ ⊤` as `X ⟶ LX ⟶ ⊤`. -/
theorem isRightAdjoint_of_convergent [HasTerminal P] [𝔓.Convergent] :
    𝔓.Beh.ι.IsRightAdjoint := by
  sorry

section Reflective

variable [Reflective 𝔓.Beh.ι]

/-- **D4.** Evaluation: the reflector onto behaviours. -/
noncomputable def L : P ⥤ 𝔓.Beh.FullSubcategory := reflector 𝔓.Beh.ι

/-- **D4.** Conversions are exactly the maps that evaluation inverts. -/
theorem conv_iff_isIso_L {X Y : P} (f : X ⟶ Y) : 𝔓.Conv f ↔ IsIso (𝔓.L.map f) := by
  sorry

/-- **D4.** The big step `X ⟶ LX` is a conversion. -/
theorem unit_mem_Conv (X : P) : 𝔓.Conv ((reflectorAdjunction 𝔓.Beh.ι).unit.app X) := by
  sorry

end Reflective

end Presentation

/-- **D5.** The dynamic picture: a category `A` of terms and reductions, with a class of steps. -/
structure DynPresentation (A : Type u) [Category.{v} A] where
  steps : MorphismProperty A

/-- **D5.** Type families over terms are covariant functors `A ⥤ Type v`. A step `s : t ⟶ t'`
appears as `coyoneda.map s.op : Hom(t', -) ⟶ Hom(t, -)`; the steps of the presentation are
the arrows isomorphic to one of these. -/
def DynPresentation.toPresentation {A : Type u} [Category.{v} A] (𝒜 : DynPresentation A) :
    Presentation (A ⥤ Type v) where
  steps := fun _ _ τ =>
    ∃ (t t' : A) (s : t ⟶ t'), 𝒜.steps s ∧
      Nonempty (Arrow.mk τ ≅ Arrow.mk (coyoneda.map s.op))

end FormalComputation
