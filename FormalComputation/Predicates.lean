import FormalComputation.LocalSystems

/-!
# Predicates as behaviours (the essay "Atoms and Probes")

The essay calls a predicate a type when it does not leak: no step joins a term that satisfies
it to one that does not. A predicate is a family whose value at each term is a subsingleton
(the evidence is a yes or nothing). For such families, being a behaviour in the sense of
Theorem A is exactly not leaking. Stated for both presentations.
-/

universe v u

namespace FormalComputation

open CategoryTheory Opposite

/-- A map between subsingletons is bijective exactly when its two ends are inhabited
together. -/
lemma bijective_of_subsingleton_iff {X Y : Type*} [Subsingleton X] [Subsingleton Y]
    (f : X → Y) : Function.Bijective f ↔ (Nonempty X ↔ Nonempty Y) := by
  constructor
  · intro hf
    exact ⟨fun ⟨x⟩ => ⟨f x⟩, fun ⟨y⟩ => ⟨(hf.2 y).choose⟩⟩
  · intro h
    refine ⟨fun a b _ => Subsingleton.elim a b, fun y => ?_⟩
    obtain ⟨x⟩ := h.2 ⟨y⟩
    exact ⟨x, Subsingleton.elim _ _⟩

variable {A : Type u} [Category.{v} A]

/-- **A predicate is a behaviour exactly when it does not leak** (covariant families). -/
theorem beh_iff_of_subsingleton_co (𝒜 : DynPresentation A) (B : A ⥤ Type v)
    [∀ t, Subsingleton (B.obj t)] :
    𝒜.toCopresentation.Beh B ↔
      ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s → (Nonempty (B.obj t) ↔ Nonempty (B.obj t')) := by
  rw [beh_iff_map_bijective_co]
  exact forall₂_congr fun t t' => forall₂_congr fun s _ => bijective_of_subsingleton_iff _

/-- **A predicate is a behaviour exactly when it does not leak** (presheaves). -/
theorem beh_iff_of_subsingleton (𝒜 : DynPresentation A) (B : Aᵒᵖ ⥤ Type v)
    [∀ t, Subsingleton (B.obj t)] :
    𝒜.toPresentation.Beh B ↔
      ∀ ⦃t t' : A⦄ (s : t ⟶ t'), 𝒜.steps s →
        (Nonempty (B.obj (op t')) ↔ Nonempty (B.obj (op t))) := by
  rw [beh_iff_map_bijective]
  exact forall₂_congr fun t t' => forall₂_congr fun s _ => bijective_of_subsingleton_iff _

end FormalComputation
