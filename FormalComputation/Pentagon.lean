import FormalComputation.LocalSystems

/-!
# Associativity and the pentagon (PROOF_MAP P1–P3)

One oriented associativity rule `(x y) z → x (y z)` on four letters gives five bracketings
and five rule instances forming a pentagon. With no equation imposed, the reduction
category is the free category on that graph (P1). A weight that counts one edge detects
the loop `top · bot⁻¹` in the reduction groupoid (P2). Imposing the pentagon gives the
four-variable Tamari poset, which has a top element; by A4 behaviours are then bare sets
(P3).

The quotient of the free category by `top = bot` being that poset is tier "stretch":
`FormalComputation/Stretch/PentQuotient.lean`.
-/

namespace FormalComputation.Pentagon

open CategoryTheory

/-- **P1.** Bracketings of four letters:
`a = ((xy)z)w`, `b = (xy)(zw)`, `c = x(y(zw))`, `d = (x(yz))w`, `e = x((yz)w)`. -/
inductive V4 | a | b | c | d | e
  deriving DecidableEq, Fintype

/-- **P1.** The five rule instances. -/
inductive Edge : V4 → V4 → Type
  | ab : Edge .a .b
  | bc : Edge .b .c
  | ad : Edge .a .d
  | de : Edge .d .e
  | ec : Edge .e .c

instance : Quiver V4 := ⟨Edge⟩

/-- **P1.** The free reduction category on the pentagon. -/
abbrev PentCat := Paths V4

/-- A bracketing as an object of the reduction category. -/
def pv (x : V4) : PentCat := x

/-- A rule instance as a reduction. -/
def ed {x y : V4} (f : Edge x y) : pv x ⟶ pv y := (Paths.of V4).map f

/-- **P1.** The upper route `a → b → c`. -/
def top : pv .a ⟶ pv .c := ed .ab ≫ ed .bc

/-- **P1.** The lower route `a → d → e → c`. -/
def bot : pv .a ⟶ pv .c := ed .ad ≫ ed .de ≫ ed .ec

/-- **P2.** Weight 1 on `ab`, 0 elsewhere, as a functor to the one-object groupoid on `ℤ`. -/
def wt : PentCat ⥤ SingleObj (Multiplicative ℤ) :=
  Paths.lift
    { obj := fun _ => SingleObj.star _
      map := fun {x y} (f : Edge x y) =>
        match f with
        | .ab => (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ)
        | _ => (1 : Multiplicative ℤ) }

/-- **P2.** The weight tells the two routes apart. -/
theorem wt_top_ne_wt_bot : wt.map top ≠ wt.map bot := by
  sorry

/-- **P2.** Hence `top` and `bot` stay distinct in the reduction groupoid: the pentagon is a
loop there. -/
theorem top_ne_bot_localized :
    (⊤ : MorphismProperty PentCat).Q.map top ≠ (⊤ : MorphismProperty PentCat).Q.map bot := by
  sorry

/-- The dynamic presentation in which every reduction is a step. -/
def pentDyn : DynPresentation PentCat := ⟨⊤⟩

/-- **P2 (added).** With A1: a behaviour on which the two routes act differently. Evaluation
of `((xy)z)w` remembers which way one reduced. -/
theorem exists_beh_top_ne_bot :
    ∃ B : PentCat ⥤ Type, pentDyn.toPresentation.Beh B ∧ B.map top ≠ B.map bot := by
  sorry

/-- **P3.** The four-variable Tamari order, on a copy of the vertex type (so that its
category structure does not clash with the free one). -/
def Tamari4 := V4

namespace Tamari4

/-- `x ≤ y` in the pentagon order `a ≤ b ≤ c`, `a ≤ d ≤ e ≤ c`. -/
def leb : V4 → V4 → Bool
  | .a, _ => true
  | .b, .b | .b, .c => true
  | .d, .d | .d, .e | .d, .c => true
  | .e, .e | .e, .c => true
  | .c, .c => true
  | _, _ => false

theorem leb_refl : ∀ x, leb x x = true := by decide
theorem leb_trans : ∀ x y z, leb x y = true → leb y z = true → leb x z = true := by decide
theorem leb_antisymm : ∀ x y, leb x y = true → leb y x = true → x = y := by decide
theorem leb_c : ∀ x, leb x .c = true := by decide

/-- **P3.** The Tamari partial order. -/
instance : PartialOrder Tamari4 where
  le x y := leb x y = true
  le_refl := leb_refl
  le_trans := leb_trans
  le_antisymm := leb_antisymm

/-- **P3.** Its top is `c`, the right-bracketed form. -/
instance : OrderTop Tamari4 where
  top := V4.c
  le_top := leb_c

end Tamari4

/-- **P3 (added).** With A4: over the Tamari poset, where every reduction is a step,
behaviours are bare sets. -/
theorem tamari_beh_bare :
    Nonempty ((⟨⊤⟩ : DynPresentation Tamari4).toPresentation.Beh.FullSubcategory ≌ Type) := by
  sorry

end FormalComputation.Pentagon
