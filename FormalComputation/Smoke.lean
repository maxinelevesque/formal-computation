import Mathlib.CategoryTheory.Category.Basic

/-! Step 1 smoke test: the project builds against Mathlib. Removed once the skeleton lands. -/

open CategoryTheory

example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f
