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
    S ≤ lOrth T ↔ T ≤ rOrth S :=
  ⟨fun h _ _ p hp _ _ e he => h e he p hp, fun h _ _ e he _ _ p hp => h p hp e he⟩

/-! ### O4: closure properties of the right class -/

/-- **O4.** Isomorphisms are in every right class. -/
theorem rOrth_of_isIso (S : MorphismProperty C) {X Y : C} (p : X ⟶ Y) [IsIso p] :
    rOrth S p := by
  intro A B e _ u w h
  refine ⟨w ≫ inv p, ⟨?_, by simp⟩, ?_⟩
  · rw [← Category.assoc, ← h]
    simp
  · rintro d ⟨-, hd⟩
    rw [← hd]
    simp

/-- Left orthogonality to `e` is closed under composition on the right. -/
theorem Orth.comp_right {A B X Y Z : C} {e : A ⟶ B} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : Orth e p) (hq : Orth e q) : Orth e (p ≫ q) := by
  intro u w h
  obtain ⟨d₁, ⟨h₁, h₁'⟩, hd₁⟩ := hq (u ≫ p) w ((Category.assoc _ _ _).trans h)
  obtain ⟨d, ⟨h₂, h₂'⟩, hd⟩ := hp u d₁ h₁.symm
  refine ⟨d, ⟨h₂, by rw [← Category.assoc, h₂', h₁']⟩, ?_⟩
  rintro d' ⟨k, k'⟩
  apply hd d'
  refine ⟨k, ?_⟩
  apply hd₁ (d' ≫ p)
  exact ⟨by rw [← Category.assoc, k], by rw [Category.assoc, k']⟩

/-- **O4.** The right class is closed under composition. -/
theorem rOrth_comp (S : MorphismProperty C) {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) :
    rOrth S p → rOrth S q → rOrth S (p ≫ q) :=
  fun hp hq _ _ e he => (hp e he).comp_right (hq e he)

/-- **O4.** The right class is stable under base change (substitution). In the square
`fst ≫ f = snd ≫ g`, `fst` is the base change of `g` along `f`. -/
theorem rOrth_of_isPullback (S : MorphismProperty C) {W X Y Z : C} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback fst snd f g) :
    rOrth S g → rOrth S fst := by
  intro hg A B e he u w h
  obtain ⟨d₁, ⟨h₁, h₁'⟩, hd₁⟩ := hg e he (u ≫ snd) (w ≫ f) (by
    rw [Category.assoc, ← sq.w, ← Category.assoc, h, Category.assoc])
  refine ⟨sq.lift w d₁ h₁'.symm, ⟨?_, sq.lift_fst _ _ _⟩, ?_⟩
  · apply sq.hom_ext
    · rw [Category.assoc, sq.lift_fst, h]
    · rw [Category.assoc, sq.lift_snd, h₁]
  · rintro d ⟨k, k'⟩
    apply sq.hom_ext
    · rw [sq.lift_fst, k']
    · rw [sq.lift_snd]
      apply hd₁
      exact ⟨by rw [← Category.assoc, k], by rw [Category.assoc, ← sq.w, ← Category.assoc, k']⟩

/-- **O4.** Left cancellation: if `p ≫ q` and `q` are in the right class, so is `p`. -/
theorem rOrth_cancel (S : MorphismProperty C) {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) :
    rOrth S (p ≫ q) → rOrth S q → rOrth S p := by
  intro hpq hq A B e he u w h
  obtain ⟨d, ⟨h₁, h₁'⟩, hd⟩ := hpq e he u (w ≫ q) (by rw [← Category.assoc, h, Category.assoc])
  obtain ⟨-, -, hd'⟩ := hq e he (u ≫ p) (w ≫ q) (by rw [h, Category.assoc])
  have hdp : d ≫ p = w :=
    (hd' (d ≫ p) ⟨by rw [← Category.assoc, h₁], by rw [Category.assoc, h₁']⟩).trans
      (hd' w ⟨h.symm, rfl⟩).symm
  refine ⟨d, ⟨h₁, hdp⟩, ?_⟩
  rintro d' ⟨k, k'⟩
  exact hd d' ⟨k, by rw [← Category.assoc, k']⟩

/-- **O5.** The diagonal of a map in the right class is in the right class
(equality types of type families are type families). -/
theorem rOrth_diagonal [HasPullbacks C] (S : MorphismProperty C) {X Y : C} (p : X ⟶ Y) :
    rOrth S p → rOrth S (pullback.diagonal p) := by
  intro hp A B e he u w h
  have hfst : e ≫ w ≫ pullback.fst p p = u := by
    rw [← Category.assoc, ← h, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hsnd : e ≫ w ≫ pullback.snd p p = u := by
    rw [← Category.assoc, ← h, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have heq : w ≫ pullback.fst p p = w ≫ pullback.snd p p := by
    obtain ⟨d, -, hd⟩ := hp e he u (w ≫ pullback.fst p p ≫ p) (by
      rw [← hfst]
      simp only [Category.assoc])
    rw [hd _ ⟨hfst, by simp only [Category.assoc]⟩,
      hd _ ⟨hsnd, by rw [Category.assoc, pullback.condition]⟩]
  refine ⟨w ≫ pullback.fst p p, ⟨hfst, ?_⟩, ?_⟩
  · apply pullback.hom_ext
    · simp [pullback.diagonal_fst]
    · simp [pullback.diagonal_snd, heq]
  · rintro d ⟨-, hd⟩
    rw [← hd]
    simp [pullback.diagonal_fst]

/-- **O6.** An adjunction transposes orthogonality. -/
theorem orth_adj {D : Type u'} [Category.{v'} D] {G : C ⥤ D} {R : D ⥤ C} (adj : G ⊣ R)
    {A B : C} (e : A ⟶ B) {X Y : D} (q : X ⟶ Y) :
    Orth (G.map e) q ↔ Orth e (R.map q) := by
  constructor
  · intro H u' w' h
    obtain ⟨d, ⟨hd₁, hd₂⟩, hd⟩ :=
      H ((adj.homEquiv _ _).symm u') ((adj.homEquiv _ _).symm w') (by
        rw [← adj.homEquiv_naturality_right_symm, h, adj.homEquiv_naturality_left_symm])
    refine ⟨adj.homEquiv _ _ d, ⟨?_, ?_⟩, ?_⟩
    · rw [← adj.homEquiv_naturality_left, hd₁, Equiv.apply_symm_apply]
    · rw [← adj.homEquiv_naturality_right, hd₂, Equiv.apply_symm_apply]
    · rintro d' ⟨h₁, h₂⟩
      rw [← (adj.homEquiv _ _).apply_symm_apply d',
        hd ((adj.homEquiv _ _).symm d')
          ⟨by rw [← adj.homEquiv_naturality_left_symm, h₁],
            by rw [← adj.homEquiv_naturality_right_symm, h₂]⟩]
  · intro H u w h
    obtain ⟨d, ⟨hd₁, hd₂⟩, hd⟩ :=
      H (adj.homEquiv _ _ u) (adj.homEquiv _ _ w) (by
        rw [← adj.homEquiv_naturality_right, h, adj.homEquiv_naturality_left])
    refine ⟨(adj.homEquiv _ _).symm d, ⟨?_, ?_⟩, ?_⟩
    · rw [← adj.homEquiv_naturality_left_symm, hd₁, Equiv.symm_apply_apply]
    · rw [← adj.homEquiv_naturality_right_symm, hd₂, Equiv.symm_apply_apply]
    · rintro d' ⟨h₁, h₂⟩
      rw [← (adj.homEquiv _ _).symm_apply_apply d',
        hd (adj.homEquiv _ _ d')
          ⟨by rw [← adj.homEquiv_naturality_left, h₁],
            by rw [← adj.homEquiv_naturality_right, h₂]⟩]

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
  constructor
  · intro h x
    constructor
    · rintro ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ hd
      have hd' : e ≫ d₁ = e ≫ d₂ := congrArg Subtype.val hd
      obtain ⟨d, -, hu⟩ := h (e ≫ d₁) x (by rw [Category.assoc, h₁])
      apply Subtype.ext
      exact (hu d₁ ⟨rfl, h₁⟩).trans (hu d₂ ⟨hd'.symm, h₂⟩).symm
    · rintro ⟨s, hs⟩
      obtain ⟨d, ⟨hd₁, hd₂⟩, -⟩ := h s x hs
      exact ⟨⟨d, hd₂⟩, Subtype.ext hd₁⟩
  · intro h u w huw
    obtain ⟨⟨d, hd⟩, hd'⟩ := (h w).2 ⟨u, huw⟩
    have hd₁ : e ≫ d = u := congrArg Subtype.val hd'
    refine ⟨d, ⟨hd₁, hd⟩, ?_⟩
    rintro d' ⟨h₁, h₂⟩
    exact congrArg Subtype.val ((h w).1
      (show restrict p e w ⟨d', h₂⟩ = restrict p e w ⟨d, hd⟩ from
        Subtype.ext (h₁.trans hd₁.symm)))

/-! ### O8: coercion and its functoriality -/

/-- Identities are left orthogonal to everything. -/
theorem Orth.id {X Y T : C} (p : X ⟶ Y) : Orth (𝟙 T) p := by
  intro u w h
  refine ⟨u, ⟨Category.id_comp _, by rw [h, Category.id_comp]⟩, ?_⟩
  rintro d ⟨hd, -⟩
  rw [← hd, Category.id_comp]

/-- Left orthogonality to a fixed `p` is closed under composition. -/
theorem Orth.comp {X Y T T' T'' : C} {e : T ⟶ T'} {e' : T' ⟶ T''} {p : X ⟶ Y}
    (h : Orth e p) (h' : Orth e' p) : Orth (e ≫ e') p := by
  intro u w huw
  obtain ⟨d₁, ⟨h₁, h₁'⟩, hd₁⟩ := h u (e' ≫ w) (huw.trans (Category.assoc _ _ _))
  obtain ⟨d, ⟨h₂, h₂'⟩, hd⟩ := h' d₁ w h₁'
  refine ⟨d, ⟨by rw [Category.assoc, h₂, h₁], h₂'⟩, ?_⟩
  rintro d' ⟨k, k'⟩
  apply hd d'
  refine ⟨?_, k'⟩
  apply hd₁ (e' ≫ d')
  exact ⟨by rw [← Category.assoc, k], by rw [Category.assoc, k']⟩

/-- **O8.** Coercion along `e` in the family `p`: the unique filler, as a map of fibres. -/
noncomputable def coerce {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) : Sec p (e ≫ x) → Sec p x :=
  (Equiv.ofBijective _ ((orth_iff_restrict_bijective e p).1 h x)).symm

/-- **O8.** Coercion is a left inverse of restriction. -/
theorem coerce_restrict {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) (d : Sec p x) : coerce h x (restrict p e x d) = d :=
  Equiv.ofBijective_symm_apply_apply _ _ d

/-- **O8.** Coercion is a right inverse of restriction. -/
theorem restrict_coerce {X Y T T' : C} {e : T ⟶ T'} {p : X ⟶ Y} (h : Orth e p)
    (x : T' ⟶ Y) (d : Sec p (e ≫ x)) : restrict p e x (coerce h x d) = d :=
  Equiv.ofBijective_apply_symm_apply _ _ d

/-- **O8.** Restriction along an identity is the identity (on underlying maps). -/
theorem restrict_id {X Y T : C} (p : X ⟶ Y) (x : T ⟶ Y) (d : Sec p x) :
    (restrict p (𝟙 T) x d).1 = d.1 :=
  Category.id_comp _

/-- **O8.** Restriction is functorial (on underlying maps). -/
theorem restrict_comp {X Y T T' T'' : C} (p : X ⟶ Y) (e : T ⟶ T') (e' : T' ⟶ T'')
    (x : T'' ⟶ Y) (d : Sec p x) :
    (restrict p (e ≫ e') x d).1 = (restrict p e (e' ≫ x) (restrict p e' x d)).1 :=
  Category.assoc _ _ _

/-- **O8.** Coercion along an identity is the identity (on underlying maps). -/
theorem coerce_id {X Y T : C} {p : X ⟶ Y} (h : Orth (𝟙 T) p) (x : T ⟶ Y)
    (d : Sec p (𝟙 T ≫ x)) : (coerce h x d).1 = d.1 :=
  (Category.id_comp (coerce h x d).1).symm.trans (congrArg Subtype.val (restrict_coerce h x d))

/-- **O8.** Coercion along `e ≫ e'` is coercion along `e`, then along `e'`
(on underlying maps; the cast is `(e ≫ e') ≫ x = e ≫ (e' ≫ x)`). -/
theorem coerce_comp {X Y T T' T'' : C} {e : T ⟶ T'} {e' : T' ⟶ T''} {p : X ⟶ Y}
    (h : Orth e p) (h' : Orth e' p) (x : T'' ⟶ Y) (d : Sec p ((e ≫ e') ≫ x)) :
    (coerce (h.comp h') x d).1 =
      (coerce h' x (coerce h (e' ≫ x) ⟨d.1, d.2.trans (Category.assoc _ _ _)⟩)).1 := by
  generalize hc₁ : coerce h (e' ≫ x) ⟨d.1, d.2.trans (Category.assoc _ _ _)⟩ = c₁
  have h₁ : e ≫ c₁.1 = d.1 := by
    rw [← hc₁]
    exact congrArg Subtype.val
      (restrict_coerce h (e' ≫ x) ⟨d.1, d.2.trans (Category.assoc _ _ _)⟩)
  have h₂ : e' ≫ (coerce h' x c₁).1 = c₁.1 :=
    congrArg Subtype.val (restrict_coerce h' x c₁)
  have hr : restrict p (e ≫ e') x (coerce h' x c₁) = d := by
    apply Subtype.ext
    show (e ≫ e') ≫ (coerce h' x c₁).1 = d.1
    rw [Category.assoc, h₂, h₁]
  rw [← hr, coerce_restrict]

/-- **O9 (helper).** Orthogonality to `X ⟶ ⊤` is bijectivity of precomposition into `X`. -/
theorem orth_terminal_iff [HasTerminal C] {A B X : C} (f : A ⟶ B) :
    Orth f (terminal.from X) ↔ Function.Bijective (fun g : B ⟶ X => f ≫ g) := by
  constructor
  · intro h
    constructor
    · intro g₁ g₂ hg
      obtain ⟨d, -, hd⟩ := h (f ≫ g₁) (terminal.from B) (terminal.hom_ext _ _)
      exact (hd g₁ ⟨rfl, terminal.hom_ext _ _⟩).trans
        (hd g₂ ⟨hg.symm, terminal.hom_ext _ _⟩).symm
    · intro u
      obtain ⟨d, ⟨hd, -⟩, -⟩ := h u (terminal.from B) (terminal.hom_ext _ _)
      exact ⟨d, hd⟩
  · intro h u w _
    obtain ⟨d, hd⟩ := h.2 u
    refine ⟨d, ⟨hd, terminal.hom_ext _ _⟩, ?_⟩
    rintro d' ⟨hd', -⟩
    exact h.1 (hd'.trans hd.symm)

/-- **O9.** `X ⟶ ⊤` is in the right class exactly when `X` is local. -/
theorem rOrth_terminal_iff_isLocal [HasTerminal C] (S : MorphismProperty C) (X : C) :
    rOrth S (terminal.from X) ↔ S.isLocal X :=
  ⟨fun h _ _ f hf => (orth_terminal_iff f).1 (h f hf),
    fun h _ _ f hf => (orth_terminal_iff f).2 (h f hf)⟩

/-- Isomorphisms are in every left class. -/
theorem lOrth_of_isIso (T : MorphismProperty C) {A B : C} (e : A ⟶ B) [IsIso e] :
    lOrth T e := by
  intro X Y p _ u w h
  refine ⟨inv e ≫ u, ⟨by simp, ?_⟩, ?_⟩
  · rw [Category.assoc, h]
    simp
  · rintro d ⟨hd, -⟩
    rw [← hd]
    simp

end FormalComputation
