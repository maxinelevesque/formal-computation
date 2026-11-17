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
theorem steps_le_E : 𝔓.steps ≤ 𝔓.E :=
  (le_lOrth_iff_le_rOrth 𝔓.steps 𝔓.M).2 le_rfl

/-- **D3.** Every computation is a conversion. -/
theorem E_le_Conv [HasTerminal P] : 𝔓.E ≤ 𝔓.Conv := by
  intro X Y f hf Z hZ
  exact (orth_terminal_iff f).1 (hf _ ((rOrth_terminal_iff_isLocal 𝔓.steps Z).2 hZ))

/-- **D3.** Behaviours are the objects whose map to `⊤` is in `M`. -/
theorem beh_iff_M [HasTerminal P] (X : P) : 𝔓.Beh X ↔ 𝔓.M (terminal.from X) :=
  (rOrth_terminal_iff_isLocal 𝔓.steps X).symm

/-- Any map to `⊤` in `M` has a behaviour as its source. -/
theorem beh_of_M [HasTerminal P] {Z : P} (p : Z ⟶ ⊤_ P) (hp : 𝔓.M p) : 𝔓.Beh Z := by
  rw [beh_iff_M, terminal.hom_ext (terminal.from Z) p]
  exact hp

/-- **D3.** Conversions satisfy 2-out-of-3. -/
instance : 𝔓.Conv.HasTwoOutOfThreeProperty :=
  inferInstanceAs (𝔓.Beh.isLocal).HasTwoOutOfThreeProperty

/-- Conversions, described through the inclusion of behaviours (the form Mathlib's Bousfield
localization lemmas use). -/
theorem conv_iff_range {X Y : P} (f : X ⟶ Y) :
    𝔓.Conv f ↔ ObjectProperty.isLocal (· ∈ Set.range 𝔓.Beh.ι.obj) f := by
  constructor
  · rintro hf _ ⟨Z, rfl⟩
    exact hf _ Z.property
  · intro hf Z hZ
    exact hf Z ⟨⟨Z, hZ⟩, rfl⟩

/-- **D4.** The size condition: `(E, M)` factors every map. -/
class Convergent : Prop where
  fac : 𝔓.E.HasFactorization 𝔓.M

attribute [instance] Convergent.fac

/-- **D4 (added).** What convergence buys: with a terminal object, it makes behaviours
reflective, i.e. every description has a denotation. Factor `X ⟶ ⊤` as `X ⟶ LX ⟶ ⊤`. -/
theorem isRightAdjoint_of_convergent [HasTerminal P] [𝔓.Convergent] :
    𝔓.Beh.ι.IsRightAdjoint := by
  let F := fun X : P => MorphismProperty.factorizationData 𝔓.E 𝔓.M (terminal.from X)
  let Lobj : P → 𝔓.Beh.FullSubcategory := fun X => ⟨(F X).Z, 𝔓.beh_of_M _ (F X).hp⟩
  let e : ∀ X Y, (Lobj X ⟶ Y) ≃ (X ⟶ 𝔓.Beh.ι.obj Y) := fun X Y =>
    𝔓.Beh.fullyFaithfulι.homEquiv.trans
      (Equiv.ofBijective (fun g : (F X).Z ⟶ Y.obj => (F X).i ≫ g)
        (𝔓.E_le_Conv _ (F X).hi Y.obj Y.property))
  exact ⟨_, ⟨Adjunction.adjunctionOfEquivLeft e (fun X Y Y' g h => by
    change (F X).i ≫ (h ≫ g).hom = ((F X).i ≫ h.hom) ≫ g.hom
    exact (Category.assoc _ _ _).symm)⟩⟩

/-- **D4 (added).** Under convergence, conversions are the 2-out-of-3 closure of the
computations: any class with 2-out-of-3 that contains `E` contains every conversion.
(Conversely `E ≤ Conv` and `Conv` has 2-out-of-3, so `Conv` is the least such class.) -/
theorem conv_le_of_E_le [HasTerminal P] [𝔓.Convergent] (W : MorphismProperty P)
    [W.HasTwoOutOfThreeProperty] (hW : 𝔓.E ≤ W) : 𝔓.Conv ≤ W := by
  intro X Y f hf
  let FX := MorphismProperty.factorizationData 𝔓.E 𝔓.M (terminal.from X)
  let FY := MorphismProperty.factorizationData 𝔓.E 𝔓.M (terminal.from Y)
  have hZX : 𝔓.Beh FX.Z := 𝔓.beh_of_M _ FX.hp
  have hZY : 𝔓.Beh FY.Z := 𝔓.beh_of_M _ FY.hp
  obtain ⟨m, hm⟩ := (𝔓.E_le_Conv _ FX.hi FY.Z hZY).2 (f ≫ FY.i)
  have hm' : FX.i ≫ m = f ≫ FY.i := hm
  have h1 : 𝔓.Conv (FX.i ≫ m) := by
    rw [hm']
    exact 𝔓.Conv.comp_mem _ _ hf (𝔓.E_le_Conv _ FY.hi)
  have hmC : 𝔓.Conv m := 𝔓.Conv.of_precomp (W' := 𝔓.Conv) _ _ (𝔓.E_le_Conv _ FX.hi) h1
  haveI : IsIso m := (ObjectProperty.isLocal_iff_isIso 𝔓.Beh m hZX hZY).1 hmC
  have h2 : W (f ≫ FY.i) := by
    rw [← hm']
    exact W.comp_mem _ _ (hW _ FX.hi) (hW _ (lOrth_of_isIso 𝔓.M m))
  exact W.of_postcomp (W' := W) _ _ (hW _ FY.hi) h2

section Reflective

variable [Reflective 𝔓.Beh.ι]

/-- **D4.** Evaluation: the reflector onto behaviours. -/
noncomputable def L : P ⥤ 𝔓.Beh.FullSubcategory := reflector 𝔓.Beh.ι

/-- **D4.** Conversions are exactly the maps that evaluation inverts. -/
theorem conv_iff_isIso_L {X Y : P} (f : X ⟶ Y) : 𝔓.Conv f ↔ IsIso (𝔓.L.map f) :=
  (𝔓.conv_iff_range f).trans
    (ObjectProperty.isLocal_iff_isIso_map (reflectorAdjunction 𝔓.Beh.ι) f)

/-- **D4.** The big step `X ⟶ LX` is a conversion. -/
theorem unit_mem_Conv (X : P) : 𝔓.Conv ((reflectorAdjunction 𝔓.Beh.ι).unit.app X) :=
  (𝔓.conv_iff_range _).2 (ObjectProperty.isLocal_adj_unit_app (reflectorAdjunction 𝔓.Beh.ι) X)

end Reflective

end Presentation

/-- **D5.** The dynamic picture: a category `A` of terms and reductions, with a class of steps. -/
structure DynPresentation (A : Type u) [Category.{v} A] where
  steps : MorphismProperty A

/-- **D5.** Descriptions are presheaves `Aᵒᵖ ⥤ Type v`; a term `t` is described by `yoneda t`.
A step `s : t ⟶ t'` appears as `yoneda.map s : y t ⟶ y t'`, so computation runs forward.
The steps of the presentation are the arrows isomorphic to one of these
(`MorphismProperty.map`).

Variance: by Yoneda, maps `y t ⟶ Z` are elements of `Z t`, so an observation `Z` acts on a
step contravariantly, by `Z.map s.op : Z t' ⟶ Z t`. Behaviours are the observers for which
this is a bijection (`beh_iff_map_bijective`). -/
def DynPresentation.toPresentation {A : Type u} [Category.{v} A] (𝒜 : DynPresentation A) :
    Presentation (Aᵒᵖ ⥤ Type v) where
  steps := 𝒜.steps.map yoneda

/-- **D5 (second presentation).** Type families over terms as covariant functors `A ⥤ Type v`.
A step `s : t ⟶ t'` appears as `coyoneda.map s.op : Hom(t', -) ⟶ Hom(t, -)`, which runs from
the contractum to the redex: in this category the computations `E` point backwards, and the
cells glued along steps add predecessors. Its behaviours are the functors out of the
localization of `A` at the steps (`behEquivLocalSystemsCo`), where the presheaf
presentation's are functors out of the localization of `Aᵒᵖ`. When the steps generate `A`
the localization is a groupoid, hence isomorphic to its opposite, and the two agree; that
comparison is not formalized. This is the presentation used for families and coercion. -/
def DynPresentation.toCopresentation {A : Type u} [Category.{v} A] (𝒜 : DynPresentation A) :
    Presentation (A ⥤ Type v) where
  steps := 𝒜.steps.op.map coyoneda

end FormalComputation
