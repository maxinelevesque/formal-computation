import FormalComputation.Presentation
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Types.Basic

/-!
# Theorem A: behaviours are local systems (PROOF_MAP A1–A4)

In the dynamic picture (presheaves, `DynPresentation.toPresentation`), a behaviour is a
presheaf `B : Aᵒᵖ ⥤ Type v` on which every step acts bijectively (A1); the action of a step
`s : t ⟶ t'` is `B.map s.op : B t' ⟶ B t`, contravariant, by Yoneda. These are the functors
inverting the steps (A2), hence the functors out of the localization at the steps: local
systems (A3). If `A` has a terminal object and every map is a step, the localization is a
point and behaviours are bare sets (A4).

The same four statements hold for the covariant presentation `toCopresentation`
(suffix `Co`).
-/

universe w v u v' u'

namespace FormalComputation

open CategoryTheory Limits Opposite

/-! ### Bijectivity of precomposition is invariant under isomorphism of arrows -/

section General

variable {C : Type u} [Category.{v} C]

lemma bijective_precomp_iff {X Y X' Y' Z : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (φ : Arrow.mk f ≅ Arrow.mk f') :
    Function.Bijective (fun g : Y ⟶ Z => f ≫ g) ↔
      Function.Bijective (fun g : Y' ⟶ Z => f' ≫ g) := by
  let l : X ≅ X' := Arrow.leftFunc.mapIso φ
  let r : Y ≅ Y' := Arrow.rightFunc.mapIso φ
  have w : f ≫ r.hom = l.hom ≫ f' := (Arrow.w φ.hom).symm
  have hcomm : (fun g : Y ⟶ Z => f ≫ g) ∘ (fun g : Y' ⟶ Z => r.hom ≫ g) =
      (fun g : X' ⟶ Z => l.hom ≫ g) ∘ (fun g : Y' ⟶ Z => f' ≫ g) := by
    funext g
    simp only [Function.comp_apply, ← Category.assoc, w]
  have hr : Function.Bijective (fun g : Y' ⟶ Z => r.hom ≫ g) :=
    Function.bijective_iff_has_inverse.2 ⟨fun g => r.inv ≫ g, fun g => by simp, fun g => by simp⟩
  have hl : Function.Bijective (fun g : X' ⟶ Z => l.hom ≫ g) :=
    Function.bijective_iff_has_inverse.2 ⟨fun g => l.inv ≫ g, fun g => by simp, fun g => by simp⟩
  rw [← Function.Bijective.of_comp_iff _ hr, hcomm, Function.Bijective.of_comp_iff' hl]

/-- Locality with respect to the image of a class under a functor (`MorphismProperty.map`,
which closes the image under isomorphism of arrows). -/
lemma isLocal_map_iff {D : Type u'} [Category.{v'} D] (W : MorphismProperty C) (F : C ⥤ D)
    (Z : D) :
    (W.map F).isLocal Z ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f →
      Function.Bijective (fun g : F.obj Y ⟶ Z => F.map f ≫ g) := by
  constructor
  · intro h X Y f hf
    exact h _ (W.map_mem_map F f hf)
  · rintro h X Y f ⟨X', Y', f', hf', ⟨φ⟩⟩
    exact (bijective_precomp_iff φ).1 (h f' hf')

/-! ### A4, abstractly: inverting every map of a category with a terminal (or initial)
object gives the point -/

/-- With a terminal object `n`, the functor to the point is left adjoint to `n`. -/
def starAdjOfTerminal (n : C) (hn : IsTerminal n) :
    (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) ⊣ Functor.fromPUnit n :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun _ := hn.from X
          invFun _ := eqToHom (Subsingleton.elim _ _)
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := hn.hom_ext _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right _ _ := hn.hom_ext _ _ }

/-- With an initial object `i`, the point `i` is left adjoint to the functor to the point. -/
def fromPUnitAdjOfInitial (i : C) (hi : IsInitial i) :
    (Functor.fromPUnit i : Discrete PUnit.{w + 1} ⥤ C) ⊣ Functor.star C :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        { toFun _ := eqToHom (Subsingleton.elim _ _)
          invFun _ := hi.to Y
          left_inv _ := hi.hom_ext _ _
          right_inv _ := Subsingleton.elim _ _ }
      homEquiv_naturality_left_symm _ _ := hi.hom_ext _ _
      homEquiv_naturality_right _ _ := Subsingleton.elim _ _ }

lemma inverseImage_star_eq_top :
    (MorphismProperty.isomorphisms (Discrete PUnit.{w + 1})).inverseImage
      (Functor.star C) = ⊤ := by
  ext X Y f
  simp only [MorphismProperty.top_apply, iff_true]
  show IsIso ((Functor.star C : C ⥤ Discrete PUnit.{w + 1}).map f)
  exact ⟨⟨eqToHom (Subsingleton.elim _ _), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- **A4 (abstract).** If `C` has a terminal object, the localization at a class equal to `⊤`
is the point. -/
theorem localization_trivial_of_terminal' (W : MorphismProperty C) (hW : W = ⊤)
    (n : C) (hn : IsTerminal n) :
    Nonempty (W.Localization ≌ Discrete PUnit.{w + 1}) := by
  subst hW
  let adj : (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) ⊣ Functor.fromPUnit n :=
    starAdjOfTerminal n hn
  haveI : (Functor.fromPUnit n : Discrete PUnit.{w + 1} ⥤ C).Full :=
    ⟨fun {_ _} _ => ⟨eqToHom (Subsingleton.elim _ _), hn.hom_ext _ _⟩⟩
  haveI : (Functor.fromPUnit n : Discrete PUnit.{w + 1} ⥤ C).Faithful :=
    ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩
  haveI : (Functor.star C : C ⥤ Discrete PUnit.{w + 1}).IsLocalization ⊤ := by
    have hW : (MorphismProperty.isomorphisms (Discrete PUnit.{w + 1})).inverseImage
        (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) = ⊤ := inverseImage_star_eq_top
    rw [← hW]
    exact adj.isLocalization
  exact ⟨Localization.uniq (⊤ : MorphismProperty C).Q
    (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) ⊤⟩

/-- **A4 (abstract, dual).** The same with an initial object. -/
theorem localization_trivial_of_initial' (W : MorphismProperty C) (hW : W = ⊤)
    (i : C) (hi : IsInitial i) :
    Nonempty (W.Localization ≌ Discrete PUnit.{w + 1}) := by
  subst hW
  let adj : (Functor.fromPUnit i : Discrete PUnit.{w + 1} ⥤ C) ⊣ Functor.star C :=
    fromPUnitAdjOfInitial i hi
  haveI : (Functor.fromPUnit i : Discrete PUnit.{w + 1} ⥤ C).Full :=
    ⟨fun {_ _} _ => ⟨eqToHom (Subsingleton.elim _ _), hi.hom_ext _ _⟩⟩
  haveI : (Functor.fromPUnit i : Discrete PUnit.{w + 1} ⥤ C).Faithful :=
    ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩
  haveI : (Functor.star C : C ⥤ Discrete PUnit.{w + 1}).IsLocalization ⊤ := by
    have hW : (MorphismProperty.isomorphisms (Discrete PUnit.{w + 1})).inverseImage
        (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) = ⊤ := inverseImage_star_eq_top
    rw [← hW]
    exact adj.isLocalization'
  exact ⟨Localization.uniq (⊤ : MorphismProperty C).Q
    (Functor.star C : C ⥤ Discrete PUnit.{w + 1}) ⊤⟩

end General

variable {A : Type u} [Category.{v} A]

/-! ### The presheaf presentation (main) -/

/-- **A1.** A presheaf is a behaviour exactly when every step acts on it bijectively. The
action of `s : t ⟶ t'` is `B.map s.op : B t' ⟶ B t` (Yoneda). -/
theorem beh_iff_map_bijective (𝒜 : DynPresentation A) (B : Aᵒᵖ ⥤ Type v) :
    𝒜.toPresentation.Beh B ↔
      ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s → Function.Bijective (B.map s.op) := by
  refine (isLocal_map_iff 𝒜.steps yoneda B).trans
    (forall₂_congr fun t t' => forall₂_congr fun s _ => ?_)
  have : (fun g : yoneda.obj t' ⟶ B => yoneda.map s ≫ g) =
      yonedaEquiv.symm ∘ B.map s.op ∘ yonedaEquiv := by
    funext g
    simp only [Function.comp_apply]
    rw [yonedaEquiv_naturality, Equiv.symm_apply_apply]
  rw [this, Function.Bijective.of_comp_iff' yonedaEquiv.symm.bijective,
    Function.Bijective.of_comp_iff _ yonedaEquiv.bijective]

lemma beh_eq_isInvertedBy (𝒜 : DynPresentation A) :
    𝒜.toPresentation.Beh = fun B : Aᵒᵖ ⥤ Type v => 𝒜.steps.op.IsInvertedBy B := by
  funext B
  apply propext
  rw [beh_iff_map_bijective]
  constructor
  · intro h X Y f hf
    exact (isIso_iff_bijective _).2 (h f.unop hf)
  · intro h t t' s hs
    exact (isIso_iff_bijective _).1 (h s.op hs)

/-- **A2.** Behaviours are the presheaves inverting the steps. -/
noncomputable def behEquivInverting (𝒜 : DynPresentation A) :
    𝒜.toPresentation.Beh.FullSubcategory ≌ 𝒜.steps.op.FunctorsInverting (Type v) := by
  have hPQ := beh_eq_isInvertedBy 𝒜
  haveI : (ObjectProperty.ιOfLE hPQ.le).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hPQ.le).2
      (hPQ.ge.trans (ObjectProperty.le_isoClosure _))
  exact (ObjectProperty.ιOfLE hPQ.le).asEquivalence

/-- **A3. Theorem A.** Behaviours are local systems: functors out of the localization of
`Aᵒᵖ` at the (opposites of the) steps. -/
noncomputable def behEquivLocalSystems (𝒜 : DynPresentation A) :
    𝒜.toPresentation.Beh.FullSubcategory ≌ (𝒜.steps.op.Localization ⥤ Type v) :=
  (behEquivInverting 𝒜).trans
    (Localization.Construction.whiskeringLeftEquivalence 𝒜.steps.op (Type v)).symm

/-- **A4.** If `A` has a terminal object, inverting every map gives the point. -/
theorem localization_trivial_of_terminal (n : A) (hn : IsTerminal n) :
    Nonempty ((⊤ : MorphismProperty A).Localization ≌ Discrete PUnit.{w + 1}) :=
  localization_trivial_of_terminal' ⊤ rfl n hn

/-- **A4.** So if every map is a step and `A` has a terminal object, behaviours are bare
sets: evaluation is path-independent. -/
theorem beh_equiv_type_of_terminal (𝒜 : DynPresentation A) (h : 𝒜.steps = ⊤)
    (n : A) (hn : IsTerminal n) :
    Nonempty (𝒜.toPresentation.Beh.FullSubcategory ≌ Type v) := by
  have h' : 𝒜.steps.op = ⊤ := by
    rw [h]
    ext
    simp
  obtain ⟨e⟩ : Nonempty (𝒜.steps.op.Localization ≌ Discrete PUnit.{1}) :=
    localization_trivial_of_initial' _ h' (op n) (initialOpOfTerminal hn)
  exact ⟨(behEquivLocalSystems 𝒜).trans (e.congrLeft.trans Functor.equiv)⟩

/-! ### The covariant presentation -/

/-- **A1 (covariant).** A covariant family is a behaviour exactly when every step acts on it
bijectively, by `B.map s : B t ⟶ B t'`. -/
theorem beh_iff_map_bijective_co (𝒜 : DynPresentation A) (B : A ⥤ Type v) :
    𝒜.toCopresentation.Beh B ↔
      ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s → Function.Bijective (B.map s) := by
  have key : ∀ ⦃t t' : A⦄ (s : t ⟶ t'),
      Function.Bijective (fun g : coyoneda.obj (op t) ⟶ B => coyoneda.map s.op ≫ g) ↔
        Function.Bijective (B.map s) := by
    intro t t' s
    have : (fun g : coyoneda.obj (op t) ⟶ B => coyoneda.map s.op ≫ g) =
        coyonedaEquiv.symm ∘ B.map s ∘ coyonedaEquiv := by
      funext g
      simp only [Function.comp_apply]
      rw [coyonedaEquiv_naturality, Equiv.symm_apply_apply]
    rw [this, Function.Bijective.of_comp_iff' coyonedaEquiv.symm.bijective,
      Function.Bijective.of_comp_iff _ coyonedaEquiv.bijective]
  refine (isLocal_map_iff 𝒜.steps.op coyoneda B).trans ⟨fun h t t' s hs => ?_, fun h X Y f hf => ?_⟩
  · exact (key s).1 (h s.op hs)
  · exact (key f.unop).2 (h f.unop hf)

lemma beh_eq_isInvertedBy_co (𝒜 : DynPresentation A) :
    𝒜.toCopresentation.Beh = fun B : A ⥤ Type v => 𝒜.steps.IsInvertedBy B := by
  funext B
  apply propext
  rw [beh_iff_map_bijective_co]
  constructor
  · intro h X Y f hf
    exact (isIso_iff_bijective _).2 (h f hf)
  · intro h t t' s hs
    exact (isIso_iff_bijective _).1 (h s hs)

/-- **A2 (covariant).** -/
noncomputable def behEquivInvertingCo (𝒜 : DynPresentation A) :
    𝒜.toCopresentation.Beh.FullSubcategory ≌ 𝒜.steps.FunctorsInverting (Type v) := by
  have hPQ := beh_eq_isInvertedBy_co 𝒜
  haveI : (ObjectProperty.ιOfLE hPQ.le).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hPQ.le).2
      (hPQ.ge.trans (ObjectProperty.le_isoClosure _))
  exact (ObjectProperty.ιOfLE hPQ.le).asEquivalence

/-- **A3 (covariant).** Functors out of the localization of `A` at the steps. -/
noncomputable def behEquivLocalSystemsCo (𝒜 : DynPresentation A) :
    𝒜.toCopresentation.Beh.FullSubcategory ≌ (𝒜.steps.Localization ⥤ Type v) :=
  (behEquivInvertingCo 𝒜).trans
    (Localization.Construction.whiskeringLeftEquivalence 𝒜.steps (Type v)).symm

/-- **A4 (covariant).** -/
theorem beh_equiv_type_of_terminal_co (𝒜 : DynPresentation A) (h : 𝒜.steps = ⊤)
    (n : A) (hn : IsTerminal n) :
    Nonempty (𝒜.toCopresentation.Beh.FullSubcategory ≌ Type v) := by
  obtain ⟨e⟩ : Nonempty (𝒜.steps.Localization ≌ Discrete PUnit.{1}) :=
    localization_trivial_of_terminal' _ h n hn
  exact ⟨(behEquivLocalSystemsCo 𝒜).trans (e.congrLeft.trans Functor.equiv)⟩

end FormalComputation
