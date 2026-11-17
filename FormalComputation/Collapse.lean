import Mathlib

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
  sorry

/-- **C3.** The section of `forget` determined by a natural family `ρ`. -/
def Ins.sec (ρ : l ⟶ r) : Xn ⥤ Ins l r where
  obj a := ⟨a, ρ.app a⟩
  map u := ⟨u, (ρ.naturality u).symm⟩

/-- **C3. Collapse lemma.** If the section given by `ρ` is left adjoint to `forget` with
identity unit, then `ρ a` is the only arrow from `l a` to `r a`. -/
theorem collapse (ρ : l ⟶ r) (adj : Ins.sec l r ρ ⊣ Ins.forget l r)
    (hunit : ∀ a, adj.unit.app a = 𝟙 a) :
    ∀ (a : Xn) (φ : l.obj a ⟶ r.obj a), φ = ρ.app a := by
  sorry

end Inserter

section Counterexample

/-- **C4.** `I = (– × Bool)` on types. -/
def Icop : Type ⥤ Type where
  obj a := a × Bool
  map f := ↾(Prod.map f id)

/-- **C4.** The I-rule `I a ⇒ a`, interpreted by the first projection. -/
def ι : Icop ⟶ 𝟭 Type where
  app _ := ↾Prod.fst

/-- **C4.** The two reductions `I (I a) ⇒ I a` differ: one drops the outer Boolean, the
other the inner one. -/
theorem accident : Functor.whiskerLeft Icop ι ≠ Functor.whiskerRight ι Icop := by
  sorry

/-- **C4 (added).** Hence, by the collapse lemma, this model is not lax orthogonal to the
I-rule: there is no left adjoint section with identity unit. -/
theorem not_lax_orthogonal :
    ¬ ∃ adj : Ins.sec Icop (𝟭 Type) ι ⊣ Ins.forget Icop (𝟭 Type), ∀ a, adj.unit.app a = 𝟙 a := by
  sorry

end Counterexample

end FormalComputation
