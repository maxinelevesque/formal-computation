import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.ObjectProperty.Local
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Unique lifting and coercion (PROOF_MAP O1–O9)

`Orth e p` says that every commuting square from `e` to `p` has exactly one diagonal.
`rOrth S` and `lOrth T` are the two orthogonal classes. Coercion along `e` in the family
`p` is the inverse of restriction along `e`, which `Orth e p` makes a bijection.

Mathlib's `HasLiftingProperty`, `MorphismProperty.llp` and `rlp` are the existence-only
analogues; they are not used here because uniqueness is the point.
-/

universe v v' u u'

namespace FormalComputation

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- **O1.** `e` is left orthogonal to `p`: every commuting square has a unique diagonal. -/
def Orth {A B X Y : C} (e : A ⟶ B) (p : X ⟶ Y) : Prop :=
  ∀ (u : A ⟶ X) (w : B ⟶ Y), u ≫ p = e ≫ w →
    ∃! d : B ⟶ X, e ≫ d = u ∧ d ≫ p = w

/-- **O2.** The maps right orthogonal to every map in `S`. -/
def rOrth (S : MorphismProperty C) : MorphismProperty C :=
  fun _ _ p => ∀ ⦃A B : C⦄ (e : A ⟶ B), S e → Orth e p

/-- **O2.** The maps left orthogonal to every map in `T`. -/
def lOrth (T : MorphismProperty C) : MorphismProperty C :=
  fun _ _ e => ∀ ⦃X Y : C⦄ (p : X ⟶ Y), T p → Orth e p

/-- **O3.** `lOrth` and `rOrth` form a Galois connection. -/
theorem le_lOrth_iff_le_rOrth (S T : MorphismProperty C) :
    S ≤ lOrth T ↔ T ≤ rOrth S := by
  sorry

/-! ### O4: closure properties of the right class -/

/-- **O4.** Isomorphisms are in every right class. -/
theorem rOrth_of_isIso (S : MorphismProperty C) {X Y : C} (p : X ⟶ Y) [IsIso p] :
    rOrth S p := by
  sorry

/-- **O4.** The right class is closed under composition. -/
theorem rOrth_comp (S : MorphismProperty C) {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) :
    rOrth S p → rOrth S q → rOrth S (p ≫ q) := by
  sorry

/-- **O4.** The right class is stable under base change (substitution). In the square
`fst ≫ f = snd ≫ g`, `fst` is the base change of `g` along `f`. -/
theorem rOrth_of_isPullback (S : MorphismProperty C) {W X Y Z : C} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g) :
    rOrth S g → rOrth S fst := by
  sorry

/-- **O4.** Left cancellation: if `p ≫ q` and `q` are in the right class, so is `p`. -/
theorem rOrth_cancel (S : MorphismProperty C) {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) :
    rOrth S (p ≫ q) → rOrth S q → rOrth S p := by
  sorry

/-- **O5.** The diagonal of a map in the right class is in the right class
(equality types of type families are type families). -/
theorem rOrth_diagonal [HasPullbacks C] (S : MorphismProperty C) {X Y : C} (p : X ⟶ Y) :
    rOrth S p → rOrth S (pullback.diagonal p) := by
  sorry

/-- **O6.** An adjunction transposes orthogonality. -/
theorem orth_adj {D : Type u'} [Category.{v'} D] {G : C ⥤ D} {R : D ⥤ C} (adj : G ⊣ R)
    {A B : C} (e : A ⟶ B) {X Y : D} (q : X ⟶ Y) :
    Orth (G.map e) q ↔ Orth e (R.map q) := by
  sorry

/-! ### O7: sections and restriction -/

/-- **O7.** The fibre of `p` over a generalized point `x : T ⟶ Y`. -/
def Sec {X Y : C} (p : X ⟶ Y) {T : C} (x : T ⟶ Y) : Type v :=
  { d : T ⟶ X // d ≫ p = x }

/-- **O7.** Restriction (substitution) of a section along `e`. -/
def restrict {X Y : C} (p : X ⟶ Y) {T T' : C} (e : T ⟶ T') (x : T' ⟶ Y) :
    Sec p x → Sec p (e ≫ x) :=
  fun d => ⟨e ≫ d.1, by rw [Category.assoc, d.2]⟩

/-- **O7.** `e` is left orthogonal to `p` exactly when restriction along `e` is a bijection on
every fibre. -/
theorem orth_iff_restrict_bijective {X Y T T' : C} (e : T ⟶ T') (p : X ⟶ Y) :
    Orth e p ↔ ∀ x : T' ⟶ Y, Function.Bijective (restrict p e x) := by
  sorry

/-! ### O8: coercion and its functoriality -/

/-- Identities are left orthogonal to everything. -/
theorem Orth.id {X Y T : C} (p : X ⟶ Y) : Orth (𝟙 T) p := by
  sorry

/-- Left orthogonality to a fixed `p` is closed under composition. -/
theorem Orth.comp {X Y T T' T'' : C} {e : T ⟶ T'} {e' : T' ⟶ T''} {p : X ⟶ Y}
    (h : Orth e p) (h' : Orth e' p) : Orth (e ≫ e') p := by
  sorry

/-- **O8.** Coercion along `e` in the family `p`: the unique filler, as a map of fibres. -/
noncomputable def coerce {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) : Sec p (e ≫ x) → Sec p x :=
  sorry

/-- **O8.** Coercion is a left inverse of restriction. -/
theorem coerce_restrict {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) (d : Sec p x) : coerce h x (restrict p e x d) = d := by
  sorry

/-- **O8.** Coercion is a right inverse of restriction. -/
theorem restrict_coerce {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) (d : Sec p (e ≫ x)) : restrict p e x (coerce h x d) = d := by
  sorry

/-- **O8.** Restriction along an identity is the identity (on underlying maps). -/
theorem restrict_id {X Y T : C} (p : X ⟶ Y) (x : T ⟶ Y) (d : Sec p x) :
    (restrict p (𝟙 T) x d).1 = d.1 := by
  sorry

/-- **O8.** Restriction is functorial (on underlying maps). -/
theorem restrict_comp {X Y T T' T'' : C} (p : X ⟶ Y) (e : T ⟶ T') (e' : T' ⟶ T'')
    (x : T'' ⟶ Y) (d : Sec p x) :
    (restrict p (e ≫ e') x d).1 = (restrict p e (e' ≫ x) (restrict p e' x d)).1 := by
  sorry

/-- **O8.** Coercion along an identity is the identity (on underlying maps). -/
theorem coerce_id {X Y T : C} {p : X ⟶ Y} (h : Orth (𝟙 T) p) (x : T ⟶ Y)
    (d : Sec p (𝟙 T ≫ x)) : (coerce h x d).1 = d.1 := by
  sorry

/-- **O8.** Coercion along `e ≫ e'` is coercion along `e`, then along `e'`
(on underlying maps; the cast is `(e ≫ e') ≫ x = e ≫ (e' ≫ x)`). -/
theorem coerce_comp {X Y T T' T'' : C} {e : T ⟶ T'} {e' : T' ⟶ T''} {p : X ⟶ Y}
    (h : Orth e p) (h' : Orth e' p) (x : T'' ⟶ Y) (d : Sec p ((e ≫ e') ≫ x)) :
    (coerce (h.comp h') x d).1 =
      (coerce h' x (coerce h (e' ≫ x) ⟨d.1, d.2.trans (Category.assoc _ _ _)⟩)).1 := by
  sorry

/-- **O9.** `X ⟶ ⊤` is in the right class exactly when `X` is local. -/
theorem rOrth_terminal_iff_isLocal [HasTerminal C] (S : MorphismProperty C) (X : C) :
    rOrth S (terminal.from X) ↔ S.isLocal X := by
  sorry

end FormalComputation
