import FormalComputation.SKI.Types
import FormalComputation.ThreeClasses
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# SKI runs as a dynamic presentation

The category of SKI runs: objects are terms, maps are runs (paths of steps), composition is
concatenation (`Paths Tm`). The steps of the presentation are the single edges. So SKI is an
instance of `DynPresentation`, and the general results about observers apply.

Proved here:
- terms in one fibre (`Conv`) are joined by a zigzag of single steps of the run category
  (`zigzag_of_conv`);
- hence they are the same under every class of behaviours, in the sense of
  `Obs.ObsEq` (`conv_obsEq`), and isomorphic in the localization at the steps
  (`conv_iso_Q`).

The converses (from sameness under behaviours, or an isomorphism in the localization, back to
`Conv`) are not proved here.
-/

namespace FormalComputation.SKI

open CategoryTheory Relation

/-- **The category of SKI runs**: terms and paths of steps. -/
abbrev RunCat : Type := Paths Tm

/-- **SKI as a dynamic presentation**: the steps are the single edges. -/
def runDyn : DynPresentation RunCat where
  steps := fun ⦃t u⦄ p => ∃ s : Step t u, p = (Paths.of Tm).map s

/-- Terms in one fibre are joined by a zigzag of single steps of the run category. -/
theorem zigzag_of_conv {t u : Tm} (h : Conv t u) :
    EqvGen (fun a b : RunCat => ∃ s : a ⟶ b, runDyn.steps s) t u := by
  induction h with
  | rel a b hs =>
    obtain ⟨s⟩ := hs
    exact EqvGen.rel _ _ ⟨(Paths.of Tm).map s, s, rfl⟩
  | refl a => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

/-- **Sameness after running implies sameness under behaviours**: terms in one fibre are the
same under any class of observers that are behaviours of the run category. -/
theorem conv_obsEq {𝒪 : Set (RunCat ⥤ Type)}
    (hbeh : ∀ B ∈ 𝒪, runDyn.toCopresentation.Beh B) {t u : Tm} (h : Conv t u) :
    Obs.ObsEq (A := RunCat) 𝒪 t u :=
  Obs.obsEq_of_zigzag runDyn hbeh (zigzag_of_conv h)

/-- **Terms in one fibre are isomorphic in the localization at the steps.** -/
theorem conv_iso_Q {t u : Tm} (h : Conv t u) :
    Nonempty (runDyn.steps.Q.obj (t : RunCat) ≅ runDyn.steps.Q.obj u) := by
  have hz := zigzag_of_conv h
  clear h
  induction hz with
  | rel a b hs =>
    obtain ⟨s, hs⟩ := hs
    exact ⟨Localization.isoOfHom runDyn.steps.Q runDyn.steps s hs⟩
  | refl a => exact ⟨Iso.refl _⟩
  | symm a b _ ih =>
    obtain ⟨i⟩ := ih
    exact ⟨i.symm⟩
  | trans a b c _ _ ih₁ ih₂ =>
    obtain ⟨i⟩ := ih₁
    obtain ⟨j⟩ := ih₂
    exact ⟨i ≪≫ j⟩

end FormalComputation.SKI
