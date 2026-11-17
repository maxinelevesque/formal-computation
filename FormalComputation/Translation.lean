import FormalComputation.Presentation

/-!
# Theorem B: simulations (PROOF_MAP B1–B6)

A simulation between presentations is an adjunction `G ⊣ R` whose left adjoint sends steps
to computations. The right adjoint then preserves behaviours, and evaluation after `G` is
left adjoint to it on behaviours (Theorem B). Uniting rule sets intersects behaviours (B3);
adding derivable rules changes nothing (B4).

The notes define a simulation as a cocontinuous functor between presheaf categories; such a
functor has a right adjoint, so here the adjunction is taken as data.

B7 (translations and conjoints) is tier "stretch": `FormalComputation/Stretch/Conjoint.lean`.
-/

universe v v' v'' u u' u''

namespace FormalComputation

open CategoryTheory Limits

/-- **B1.** A right adjoint whose left adjoint sends `S`-maps to `S'`-conversions sends
`S'`-local objects to `S`-local objects. -/
theorem isLocal_of_adj {P : Type u} {P' : Type u'} [Category.{v} P] [Category.{v'} P']
    {G : P ⥤ P'} {R : P' ⥤ P} (adj : G ⊣ R) (S : MorphismProperty P)
    (S' : MorphismProperty P')
    (h : ∀ ⦃X Y : P⦄ (f : X ⟶ Y), S f → (S'.isLocal).isLocal (G.map f))
    (Z : P') (hZ : S'.isLocal Z) : S.isLocal (R.obj Z) := by
  sorry

/-- **B3.** Uniting rule sets intersects behaviours. -/
theorem isLocal_sup {P : Type u} [Category.{v} P] (S₁ S₂ : MorphismProperty P) :
    (S₁ ⊔ S₂).isLocal = S₁.isLocal ⊓ S₂.isLocal := by
  sorry

/-- **B4.** Completion is harmless: adding rules that are already conversions does not
change the behaviours. -/
theorem isLocal_eq_of_le_of_le_conv {P : Type u} [Category.{v} P] (S S' : MorphismProperty P)
    (h₁ : S ≤ S') (h₂ : S' ≤ (S.isLocal).isLocal) : S'.isLocal = S.isLocal := by
  sorry

/-- **B4 (added).** Adding rules that are already computations does not change the
computations either (`notes/05` §5.2, "Adding rules already in `E` changes neither `E`
nor `C`"). -/
theorem E_eq_of_le_of_le_E {P : Type u} [Category.{v} P] (𝒫 𝒫' : Presentation P)
    (h₁ : 𝒫.steps ≤ 𝒫'.steps) (h₂ : 𝒫'.steps ≤ 𝒫.E) : 𝒫'.E = 𝒫.E := by
  sorry

variable {P : Type u} {P' : Type u'} {P'' : Type u''}
  [Category.{v} P] [Category.{v'} P'] [Category.{v''} P'']

/-- **B2.** A simulation: an adjunction whose left adjoint sends steps to computations. -/
structure Simulation (𝒫 : Presentation P) (𝒫' : Presentation P') where
  G : P ⥤ P'
  R : P' ⥤ P
  adj : G ⊣ R
  steps_to_E : ∀ ⦃X Y : P⦄ (f : X ⟶ Y), 𝒫.steps f → 𝒫'.E (G.map f)

namespace Simulation

variable {𝒫 : Presentation P} {𝒫' : Presentation P'} {𝒫'' : Presentation P''}

/-- **B2.** The right adjoint, restricted to behaviours. -/
def onBeh [HasTerminal P'] (σ : Simulation 𝒫 𝒫') :
    𝒫'.Beh.FullSubcategory ⥤ 𝒫.Beh.FullSubcategory :=
  sorry

/-- **B2. Theorem B.** Evaluation after `G` is left adjoint to `R` on behaviours. -/
noncomputable def adjOnBeh [HasTerminal P'] [Reflective 𝒫'.Beh.ι] (σ : Simulation 𝒫 𝒫') :
    (𝒫.Beh.ι ⋙ σ.G ⋙ 𝒫'.L) ⊣ σ.onBeh :=
  sorry

/-- **B5.** The right adjoint preserves `M`. -/
theorem R_preserves_M (σ : Simulation 𝒫 𝒫') :
    ∀ ⦃X Y : P'⦄ (q : X ⟶ Y), 𝒫'.M q → 𝒫.M (σ.R.map q) := by
  sorry

/-- **B5.** The left adjoint preserves computations. -/
theorem G_preserves_E (σ : Simulation 𝒫 𝒫') :
    ∀ ⦃X Y : P⦄ (f : X ⟶ Y), 𝒫.E f → 𝒫'.E (σ.G.map f) := by
  sorry

/-- **B6.** The identity simulation. -/
def id (𝒫 : Presentation P) : Simulation 𝒫 𝒫 :=
  sorry

/-- **B6.** Composition of simulations. -/
def comp (σ : Simulation 𝒫 𝒫') (τ : Simulation 𝒫' 𝒫'') : Simulation 𝒫 𝒫'' :=
  sorry

end Simulation

end FormalComputation
