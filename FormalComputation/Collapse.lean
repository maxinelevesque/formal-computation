import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Types.Basic

/-!
# The collapse lemma (PROOF_MAP C1–C4)

A rule `l ⇒ r` between functors `l r : Xn ⥤ X` gives the inserter category `Ins l r` of
pairs `(a, φ : l a ⟶ r a)`. Lax orthogonality to the rule asks the forgetful functor
`Ins l r ⥤ Xn` to have a left adjoint section with identity unit. The collapse lemma says
that this forces a unique arrow `l a ⟶ r a` for every `a` (C3). The I-rule interpreted by
`(– × Bool, fst)` on types has two such arrows (C4), so it is a perfectly good model that is
not lax orthogonal to its rule.
-/

universe v₁ v₂ u₁ u₂

namespace FormalComputation

open CategoryTheory

section Inserter

variable {Xn : Type u₁} {X : Type u₂} [Category.{v₁} Xn] [Category.{v₂} X] (l r : Xn ⥤ X)

/-- **C1.** Objects of the inserter category: an object with an arrow from `l a` to `r a`. -/
structure Ins where
  a : Xn
  φ : l.obj a ⟶ r.obj a

variable {l r}

/-- **C1.** Morphisms of the inserter: maps commuting with the chosen arrows. -/
@[ext]
structure Ins.Hom (p q : Ins l r) where
  u : p.a ⟶ q.a
  w : p.φ ≫ r.map u = l.map u ≫ q.φ

/-- **C1.** The inserter category. -/
instance : Category (Ins l r) where
  Hom := Ins.Hom
  id p := ⟨𝟙 p.a, by simp⟩
  comp f g := ⟨f.u ≫ g.u, by
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% f.w, g.w]⟩
  id_comp f := Ins.Hom.ext (Category.id_comp _)
  comp_id f := Ins.Hom.ext (Category.comp_id _)
  assoc f g h := Ins.Hom.ext (Category.assoc _ _ _)

@[ext]
lemma Ins.hom_ext {p q : Ins l r} {f g : p ⟶ q} (h : f.u = g.u) : f = g :=
  Ins.Hom.ext h

variable (l r)

/-- **C1.** The forgetful functor. -/
def Ins.forget : Ins l r ⥤ Xn where
  obj p := p.a
  map f := f.u

/-- **C2.** Collapse, unfolded: if `ρ a` is compatible with every arrow `φ'` along every `u`,
then `ρ a` is the only arrow `l a ⟶ r a`. -/
theorem collapse_unfolded (ρ : ∀ a, l.obj a ⟶ r.obj a)
    (h : ∀ ⦃a a' : Xn⦄ (u : a ⟶ a') (φ' : l.obj a' ⟶ r.obj a'),
        ρ a ≫ r.map u = l.map u ≫ φ') :
    ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ a := by
  intro a φ
  simpa using (h (𝟙 a) φ).symm

/-- **C3.** The section of `forget` determined by a natural family `ρ`. -/
def Ins.sec (ρ : l ⟶ r) : Xn ⥤ Ins l r where
  obj a := ⟨a, ρ.app a⟩
  map u := ⟨u, (ρ.naturality u).symm⟩

/-- **C3″ (added).** The collapse lemma with an invertible unit in place of an identity
unit (the pseudo variant). -/
theorem collapse_of_isIso_unit (ρ : l ⟶ r) (adj : Ins.sec l r ρ ⊣ Ins.forget l r)
    (hunit : ∀ a, IsIso (adj.unit.app a)) :
    ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a := by
  apply collapse_unfolded l r (fun a => ρ.app a)
  intro a a' u φ'
  haveI := hunit a
  have hg : ((adj.homEquiv a ⟨a', φ'⟩).symm (adj.unit.app a ≫ u)).u = u := by
    have h1 := (adj.homEquiv a ⟨a', φ'⟩).apply_symm_apply (adj.unit.app a ≫ u)
    rw [adj.homEquiv_unit] at h1
    exact (cancel_epi (adj.unit.app a)).1 h1
  have := ((adj.homEquiv a ⟨a', φ'⟩).symm (adj.unit.app a ≫ u)).w
  rw [hg] at this
  exact this

/-- **C3. Collapse lemma.** If the section given by `ρ` is left adjoint to `forget` with
identity unit, then `ρ a` is the only arrow from `l a` to `r a`. -/
theorem collapse (ρ : l ⟶ r) (adj : Ins.sec l r ρ ⊣ Ins.forget l r)
    (hunit : ∀ a, adj.unit.app a = 𝟙 a) :
    ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a :=
  collapse_of_isIso_unit l r ρ adj fun a => by
    rw [hunit a]
    exact IsIso.id a

/-- **C3″ (added).** The collapse lemma with the section on the other side: a right adjoint
section with invertible counit (identity counit is the special case). -/
theorem collapse_of_isIso_counit (ρ : l ⟶ r) (adj : Ins.forget l r ⊣ Ins.sec l r ρ)
    (hcounit : ∀ a, IsIso (adj.counit.app a)) :
    ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a := by
  intro a φ
  haveI := hcounit a
  have hg : (adj.homEquiv (⟨a, φ⟩ : Ins l r) a (adj.counit.app a)).u = 𝟙 a := by
    have h1 := (adj.homEquiv (⟨a, φ⟩ : Ins l r) a).symm_apply_apply (adj.counit.app a)
    rw [adj.homEquiv_counit] at h1
    exact (cancel_mono (adj.counit.app a)).1 (h1.trans (Category.id_comp _).symm)
  have := (adj.homEquiv (⟨a, φ⟩ : Ins l r) a (adj.counit.app a)).w
  rw [hg] at this
  erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.id_comp] at this
  exact this

/-- **C3′ (added).** Conversely, if `ρ a` is the only arrow `l a ⟶ r a` for every `a`, the
section given by `ρ` is left adjoint to `forget`, with identity unit. -/
def secAdjOfUnique (ρ : l ⟶ r) (h : ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a) :
    Ins.sec l r ρ ⊣ Ins.forget l r :=
  Adjunction.mkOfHomEquiv
    { homEquiv a q :=
        { toFun f := f.u
          invFun u := ⟨u, by
            rw [h q.a q.φ]
            exact (ρ.naturality u).symm⟩
          left_inv _ := Ins.hom_ext rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := Ins.hom_ext rfl
      homEquiv_naturality_right _ _ := rfl }

/-- **C3′ (added). Characterization.** For a natural `ρ : l ⟶ r`, the section given by `ρ` is
a left adjoint of `forget` with identity unit exactly when every hom-set `X(l a, r a)` is
`{ρ a}`. The naturality of `ρ` is what makes the converse work: uniqueness at each `a` alone
does not make the squares `l a ⟶ r a'` commute. -/
theorem lax_orthogonal_iff (ρ : l ⟶ r) :
    (∃ adj : Ins.sec l r ρ ⊣ Ins.forget l r, ∀ a, adj.unit.app a = 𝟙 a) ↔
      ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a :=
  ⟨fun ⟨adj, h⟩ => collapse l r ρ adj h, fun h => ⟨secAdjOfUnique l r ρ h, fun _ => rfl⟩⟩

/-- **C3′ (added).** In that case `forget` is an equivalence: a rule that is lax orthogonal
in this sense carries no more information than its arguments. -/
theorem forget_isEquivalence_of_unique (ρ : l ⟶ r)
    (h : ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a) :
    (Ins.forget l r).IsEquivalence where
  faithful := ⟨fun {_ _} _ _ hfg => Ins.hom_ext hfg⟩
  full := ⟨fun {p q} u => ⟨⟨u, by
    rw [h p.a p.φ, h q.a q.φ]
    exact (ρ.naturality u).symm⟩, rfl⟩⟩
  essSurj := ⟨fun a => ⟨(Ins.sec l r ρ).obj a, ⟨Iso.refl _⟩⟩⟩

end Inserter

section Counterexample

/-- **C4.** `I = (– × Bool)` on types. -/
def Icop : Type ⥤ Type where
  obj a := a × Bool
  map f := ↾(Prod.map f id)

/-- **C4.** The I-rule `I a ⇒ a`, interpreted by the first projection. -/
def ι : Icop ⟶ 𝟭 Type where
  app _ := ↾Prod.fst

/-- **C4.** The two reductions `I (I a) ⇒ I a` differ at `a = Unit`. -/
theorem accident_app :
    (Functor.whiskerLeft Icop ι).app Unit ≠ (Functor.whiskerRight ι Icop).app Unit := by
  intro h
  have h1 := types_congr_hom h (((), true), false)
  change (((), true) : Unit × Bool) = ((), false) at h1
  exact absurd (congrArg Prod.snd h1) (by decide)

/-- **C4.** The two reductions `I (I a) ⇒ I a` differ: one drops the outer Boolean, the
other the inner one. -/
theorem accident : Functor.whiskerLeft Icop ι ≠ Functor.whiskerRight ι Icop :=
  fun h => accident_app (NatTrans.congr_app h Unit)

/-- **C4 (added).** Hence, by the collapse lemma, this model is not lax orthogonal to the
I-rule: there is no left adjoint section with identity unit. -/
theorem not_lax_orthogonal :
    ¬ ∃ adj : Ins.sec Icop (𝟭 Type) ι ⊣ Ins.forget Icop (𝟭 Type), ∀ a, adj.unit.app a = 𝟙 a := by
  rintro ⟨adj, hunit⟩
  apply accident_app
  have c := collapse Icop (𝟭 Type) ι adj hunit (Icop.obj Unit)
  exact (c _).trans (c _).symm

end Counterexample

end FormalComputation
