import FormalComputation.Presentation
import Mathlib.CategoryTheory.Adjunction.Restrict

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
  intro X Y f hf
  have hb := h f hf Z hZ
  have : (fun g : Y ⟶ R.obj Z => f ≫ g) =
      (adj.homEquiv X Z) ∘ (fun g' : G.obj Y ⟶ Z => G.map f ≫ g') ∘ (adj.homEquiv Y Z).symm := by
    funext g
    simp only [Function.comp_apply, adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  rw [this, Function.Bijective.of_comp_iff' (adj.homEquiv X Z).bijective,
    Function.Bijective.of_comp_iff _ (adj.homEquiv Y Z).symm.bijective]
  exact hb

/-- **B3.** Uniting rule sets intersects behaviours. -/
theorem isLocal_sup {P : Type u} [Category.{v} P] (S₁ S₂ : MorphismProperty P) :
    (S₁ ⊔ S₂).isLocal = S₁.isLocal ⊓ S₂.isLocal := by
  funext Z
  apply propext
  constructor
  · intro h
    exact ⟨fun X Y f hf => h f (Or.inl hf), fun X Y f hf => h f (Or.inr hf)⟩
  · rintro ⟨h₁, h₂⟩ X Y f (hf | hf)
    exacts [h₁ f hf, h₂ f hf]

/-- **B4.** Completion is harmless: adding rules that are already conversions does not
change the behaviours. -/
theorem isLocal_eq_of_le_of_le_conv {P : Type u} [Category.{v} P] (S S' : MorphismProperty P)
    (h₁ : S ≤ S') (h₂ : S' ≤ (S.isLocal).isLocal) : S'.isLocal = S.isLocal := by
  apply le_antisymm
  · exact MorphismProperty.isLocal_antitone h₁
  · intro Z hZ X Y f hf
    exact h₂ f hf Z hZ

/-- **B4 (added).** Adding rules that are already computations does not change the
computations either (`notes/05` §5.2, "Adding rules already in `E` changes neither `E`
nor `C`"). -/
theorem E_eq_of_le_of_le_E {P : Type u} [Category.{v} P] (𝔓 𝔓' : Presentation P)
    (h₁ : 𝔓.steps ≤ 𝔓'.steps) (h₂ : 𝔓'.steps ≤ 𝔓.E) : 𝔓'.E = 𝔓.E := by
  have hM : 𝔓'.M = 𝔓.M := by
    apply le_antisymm
    · intro X Y p hp A B e he
      exact hp e (h₁ e he)
    · exact (le_lOrth_iff_le_rOrth 𝔓'.steps 𝔓.M).1 h₂
  show lOrth 𝔓'.M = lOrth 𝔓.M
  rw [hM]

variable {P : Type u} {P' : Type u'} {P'' : Type u''}
  [Category.{v} P] [Category.{v'} P'] [Category.{v''} P'']

/-- **B2.** A simulation: an adjunction whose left adjoint sends steps to computations. -/
structure Simulation (𝔓 : Presentation P) (𝔓' : Presentation P') where
  G : P ⥤ P'
  R : P' ⥤ P
  adj : G ⊣ R
  steps_to_E : ∀ ⦃X Y : P⦄ (f : X ⟶ Y), 𝔓.steps f → 𝔓'.E (G.map f)

namespace Simulation

variable {𝔓 : Presentation P} {𝔓' : Presentation P'} {𝔓'' : Presentation P''}

/-- **B2.** The right adjoint, restricted to behaviours. -/
def onBeh [HasTerminal P'] (σ : Simulation 𝔓 𝔓') :
    𝔓'.Beh.FullSubcategory ⥤ 𝔓.Beh.FullSubcategory :=
  𝔓.Beh.lift (𝔓'.Beh.ι ⋙ σ.R) fun Z =>
    isLocal_of_adj σ.adj 𝔓.steps 𝔓'.steps
      (fun _ _ f hf => 𝔓'.E_le_Conv _ (σ.steps_to_E f hf)) Z.obj Z.property

/-- **B2. Theorem B.** Evaluation after `G` is left adjoint to `R` on behaviours. -/
noncomputable def adjOnBeh [HasTerminal P'] [Reflective 𝔓'.Beh.ι] (σ : Simulation 𝔓 𝔓') :
    (𝔓.Beh.ι ⋙ σ.G ⋙ 𝔓'.L) ⊣ σ.onBeh :=
  (σ.adj.comp (reflectorAdjunction 𝔓'.Beh.ι)).restrictFullyFaithful
    𝔓.Beh.fullyFaithfulι (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)

/-- **B5.** The right adjoint preserves `M`. -/
theorem R_preserves_M (σ : Simulation 𝔓 𝔓') :
    ∀ ⦃X Y : P'⦄ (q : X ⟶ Y), 𝔓'.M q → 𝔓.M (σ.R.map q) := by
  intro X Y q hq A B e he
  exact (orth_adj σ.adj e q).1 (σ.steps_to_E e he q hq)

/-- **B5.** The left adjoint preserves computations. -/
theorem G_preserves_E (σ : Simulation 𝔓 𝔓') :
    ∀ ⦃X Y : P⦄ (f : X ⟶ Y), 𝔓.E f → 𝔓'.E (σ.G.map f) := by
  intro X Y f hf A B q hq
  exact (orth_adj σ.adj f q).2 (hf _ (σ.R_preserves_M q hq))

/-- **B6.** The identity simulation. -/
def id (𝔓 : Presentation P) : Simulation 𝔓 𝔓 where
  G := 𝟭 P
  R := 𝟭 P
  adj := Adjunction.id
  steps_to_E _ _ f hf := 𝔓.steps_le_E f hf

/-- **B6.** Composition of simulations. -/
def comp (σ : Simulation 𝔓 𝔓') (τ : Simulation 𝔓' 𝔓'') : Simulation 𝔓 𝔓'' where
  G := σ.G ⋙ τ.G
  R := τ.R ⋙ σ.R
  adj := σ.adj.comp τ.adj
  steps_to_E _ _ f hf := τ.G_preserves_E _ (σ.steps_to_E f hf)

end Simulation

end FormalComputation
