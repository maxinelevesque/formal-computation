import FormalComputation.SKI.Types

/-!
# SKI: confluence (Church–Rosser)

Combinatory logic is confluent: two runs from one term can always be continued until they
meet. The proof is the standard one by parallel reduction, which has the diamond property.

Consequences used by the essay: a term has at most one normal form, two different normal
forms never lie in one fibre (`conv_normal_eq`), and a term converted to a normal form runs
to it (`reds_of_conv_normal`).
-/

namespace FormalComputation.SKI

open Relation

/-- One step, as a relation. -/
abbrev R1 : Tm → Tm → Prop := fun t u => Nonempty (Step t u)

/-- Running: zero or more steps. -/
abbrev Reds : Tm → Tm → Prop := ReflTransGen R1

theorem reds_appL (u : Tm) {t t' : Tm} (h : Reds t t') : Reds (t ⬝ u) (t' ⬝ u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨Step.appL u hs.some⟩

theorem reds_appR (t : Tm) {u u' : Tm} (h : Reds u u') : Reds (t ⬝ u) (t ⬝ u') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨Step.appR t hs.some⟩

theorem reds_app {t t' u u' : Tm} (h₁ : Reds t t') (h₂ : Reds u u') :
    Reds (t ⬝ u) (t' ⬝ u') :=
  (reds_appL u h₁).trans (reds_appR t' h₂)

/-- Running is a special case of conversion. -/
theorem reds_conv {t u : Tm} (h : Reds t u) : Conv t u := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ hs ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hs)

/-- Parallel reduction: contract any set of the redexes present, all at once. -/
inductive Par : Tm → Tm → Prop
  | refl (t : Tm) : Par t t
  | app {t t' u u' : Tm} : Par t t' → Par u u' → Par (t ⬝ u) (t' ⬝ u')
  | i {x x' : Tm} : Par x x' → Par (.I ⬝ x) x'
  | k {x x' : Tm} (y : Tm) : Par x x' → Par (.K ⬝ x ⬝ y) x'
  | s {x x' y y' z z' : Tm} : Par x x' → Par y y' → Par z z' →
      Par (.S ⬝ x ⬝ y ⬝ z) (x' ⬝ z' ⬝ (y' ⬝ z'))

theorem par_Kx {x b : Tm} (h : Par (.K ⬝ x) b) : ∃ x', b = .K ⬝ x' ∧ Par x x' := by
  cases h with
  | refl => exact ⟨x, rfl, .refl _⟩
  | app h₁ h₂ =>
    cases h₁
    exact ⟨_, rfl, h₂⟩

theorem par_Sx {x b : Tm} (h : Par (.S ⬝ x) b) : ∃ x', b = .S ⬝ x' ∧ Par x x' := by
  cases h with
  | refl => exact ⟨x, rfl, .refl _⟩
  | app h₁ h₂ =>
    cases h₁
    exact ⟨_, rfl, h₂⟩

theorem par_Sxy {x y b : Tm} (h : Par (.S ⬝ x ⬝ y) b) :
    ∃ x' y', b = .S ⬝ x' ⬝ y' ∧ Par x x' ∧ Par y y' := by
  cases h with
  | refl => exact ⟨x, y, rfl, .refl _, .refl _⟩
  | app h₁ h₂ =>
    obtain ⟨x', rfl, hx⟩ := par_Sx h₁
    exact ⟨x', _, rfl, hx, h₂⟩

/-- **The diamond property** of parallel reduction. -/
theorem par_diamond {a b c : Tm} (h₁ : Par a b) (h₂ : Par a c) :
    ∃ d, Par b d ∧ Par c d := by
  induction h₁ generalizing c with
  | refl t => exact ⟨c, h₂, .refl _⟩
  | app ht hu iht ihu =>
    cases h₂ with
    | refl => exact ⟨_, .refl _, .app ht hu⟩
    | app ht₂ hu₂ =>
      obtain ⟨d₁, e₁, f₁⟩ := iht ht₂
      obtain ⟨d₂, e₂, f₂⟩ := ihu hu₂
      exact ⟨_, .app e₁ e₂, .app f₁ f₂⟩
    | i hx =>
      cases ht
      obtain ⟨d, e, f⟩ := ihu hx
      exact ⟨d, .i e, f⟩
    | k y hx =>
      obtain ⟨x₁, rfl, -⟩ := par_Kx ht
      obtain ⟨d, e, f⟩ := iht (Par.app (Par.refl .K) hx)
      obtain ⟨e₁, rfl, g₁⟩ := par_Kx e
      obtain ⟨e₂, he, g₂⟩ := par_Kx f
      cases he
      exact ⟨_, .k _ g₁, g₂⟩
    | s hx hy hz =>
      obtain ⟨x₁, y₁, rfl, -, -⟩ := par_Sxy ht
      obtain ⟨d, e, f⟩ := iht (Par.app (Par.app (Par.refl .S) hx) hy)
      obtain ⟨ex, ey, rfl, gx₁, gy₁⟩ := par_Sxy e
      obtain ⟨ex', ey', he, gx₂, gy₂⟩ := par_Sxy f
      cases he
      obtain ⟨dz, ez, fz⟩ := ihu hz
      exact ⟨_, .s gx₁ gy₁ ez, .app (.app gx₂ fz) (.app gy₂ fz)⟩
  | i hx ihx =>
    cases h₂ with
    | refl => exact ⟨_, .refl _, .i hx⟩
    | app h₁' h₂' =>
      cases h₁'
      obtain ⟨d, e, f⟩ := ihx h₂'
      exact ⟨d, e, .i f⟩
    | i hx₂ => exact ihx hx₂
  | k y hx ihx =>
    cases h₂ with
    | refl => exact ⟨_, .refl _, .k y hx⟩
    | app h₁' h₂' =>
      obtain ⟨x'', rfl, hxx⟩ := par_Kx h₁'
      obtain ⟨d, e, f⟩ := ihx hxx
      exact ⟨d, e, .k _ f⟩
    | k _ hx₂ => exact ihx hx₂
  | s hx hy hz ihx ihy ihz =>
    cases h₂ with
    | refl => exact ⟨_, .refl _, .s hx hy hz⟩
    | app h₁' h₂' =>
      obtain ⟨x'', y'', rfl, hxx, hyy⟩ := par_Sxy h₁'
      obtain ⟨dx, ex, fx⟩ := ihx hxx
      obtain ⟨dy, ey, fy⟩ := ihy hyy
      obtain ⟨dz, ez, fz⟩ := ihz h₂'
      exact ⟨_, .app (.app ex ez) (.app ey ez), .s fx fy fz⟩
    | s hx₂ hy₂ hz₂ =>
      obtain ⟨dx, ex, fx⟩ := ihx hx₂
      obtain ⟨dy, ey, fy⟩ := ihy hy₂
      obtain ⟨dz, ez, fz⟩ := ihz hz₂
      exact ⟨_, .app (.app ex ez) (.app ey ez), .app (.app fx fz) (.app fy fz)⟩

theorem par_of_step {t u : Tm} (s : Step t u) : Par t u := by
  induction s with
  | i x => exact .i (.refl x)
  | k x y => exact .k y (.refl x)
  | s x y z => exact .s (.refl x) (.refl y) (.refl z)
  | appL u _ ih => exact .app ih (.refl u)
  | appR t _ ih => exact .app (.refl t) ih

theorem reds_of_par {t u : Tm} (h : Par t u) : Reds t u := by
  induction h with
  | refl => exact .refl
  | app _ _ ih₁ ih₂ => exact reds_app ih₁ ih₂
  | i _ ih => exact (reds_appR .I ih).tail ⟨Step.i _⟩
  | k y _ ih => exact (reds_appL y (reds_appR .K ih)).tail ⟨Step.k _ y⟩
  | s _ _ _ ihx ihy ihz =>
    exact (reds_app (reds_app (reds_appR .S ihx) ihy) ihz).tail ⟨Step.s _ _ _⟩

theorem reds_of_parStar {t u : Tm} (h : ReflTransGen Par t u) : Reds t u := by
  induction h with
  | refl => exact .refl
  | tail _ hp ih => exact ih.trans (reds_of_par hp)

/-- **Confluence.** Two runs from one term can be continued until they meet. -/
theorem confluent {a b c : Tm} (hb : Reds a b) (hc : Reds a c) :
    ∃ d, Reds b d ∧ Reds c d := by
  have star : ∀ {x y : Tm}, Reds x y → ReflTransGen Par x y := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (par_of_step hs.some)
  have hb' := star hb
  have hc' := star hc
  obtain ⟨d, h₁, h₂⟩ := church_rosser (fun a b c hab hac => by
    obtain ⟨d, e, f⟩ := par_diamond hab hac
    exact ⟨d, ReflGen.single e, ReflTransGen.single f⟩) hb' hc'
  exact ⟨d, reds_of_parStar h₁, reds_of_parStar h₂⟩

/-- **Church–Rosser.** Terms in one fibre run to a common term. -/
theorem conv_join {t u : Tm} (h : Conv t u) : ∃ d, Reds t d ∧ Reds u d := by
  induction h with
  | rel x y h => exact ⟨y, .single h, .refl⟩
  | refl x => exact ⟨x, .refl, .refl⟩
  | symm x y _ ih =>
    obtain ⟨d, h₁, h₂⟩ := ih
    exact ⟨d, h₂, h₁⟩
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨d₁, a₁, b₁⟩ := ih₁
    obtain ⟨d₂, a₂, b₂⟩ := ih₂
    obtain ⟨e, c₁, c₂⟩ := confluent b₁ a₂
    exact ⟨e, a₁.trans c₁, b₂.trans c₂⟩

/-- A **normal form**: a term with no redex. -/
def IsNormal (t : Tm) : Prop := ∀ u, Step t u → False

theorem reds_normal {t u : Tm} (ht : IsNormal t) (h : Reds t u) : u = t := by
  rcases ReflTransGen.cases_head h with rfl | ⟨c, ⟨s⟩, _⟩
  · rfl
  · exact (ht c s).elim

/-- **Two different normal forms never lie in one fibre.** -/
theorem conv_normal_eq {t u : Tm} (h : Conv t u) (ht : IsNormal t) (hu : IsNormal u) :
    t = u := by
  obtain ⟨d, a, b⟩ := conv_join h
  rw [← reds_normal ht a, ← reds_normal hu b]

/-- A term in the fibre of a normal form runs to it. -/
theorem reds_of_conv_normal {u r : Tm} (h : Conv u r) (hr : IsNormal r) : Reds u r := by
  obtain ⟨d, a, b⟩ := conv_join h
  rw [reds_normal hr b] at a
  exact a

/-! Deciding normality of concrete terms. -/

/-- Whether the root of a term is a redex. -/
def isRedex : Tm → Bool
  | .app .I _ => true
  | .app (.app .K _) _ => true
  | .app (.app (.app .S _) _) _ => true
  | _ => false

/-- Whether a term contains a redex. -/
def hasRedex : Tm → Bool
  | .app f a => isRedex (.app f a) || hasRedex f || hasRedex a
  | _ => false

theorem hasRedex_of_step {t u : Tm} (s : Step t u) : hasRedex t = true := by
  induction s with
  | i x => simp [hasRedex, isRedex]
  | k x y => simp [hasRedex, isRedex]
  | s x y z => simp [hasRedex, isRedex]
  | appL u _ ih => simp [hasRedex, ih]
  | appR t _ ih => simp [hasRedex, ih]

theorem isNormal_of_hasRedex {t : Tm} (h : hasRedex t = false) : IsNormal t :=
  fun _ s => by simp [hasRedex_of_step s] at h

theorem isNormal_I : IsNormal .I := isNormal_of_hasRedex rfl
theorem isNormal_K : IsNormal .K := isNormal_of_hasRedex rfl
theorem isNormal_SKK : IsNormal (.S ⬝ .K ⬝ .K) := isNormal_of_hasRedex rfl
theorem isNormal_SKS : IsNormal (.S ⬝ .K ⬝ .S) := isNormal_of_hasRedex rfl

/-- **`I`, `S K K` and `S K S` lie in three different fibres** (the essay's three
equalities: sameness after running keeps them apart). -/
theorem three_fibres :
    ¬ Conv .I (.S ⬝ .K ⬝ .K) ∧ ¬ Conv .I (.S ⬝ .K ⬝ .S) ∧
      ¬ Conv (.S ⬝ .K ⬝ .K) (.S ⬝ .K ⬝ .S) :=
  ⟨fun h => absurd (conv_normal_eq h isNormal_I isNormal_SKK) (by decide),
   fun h => absurd (conv_normal_eq h isNormal_I isNormal_SKS) (by decide),
   fun h => absurd (conv_normal_eq h isNormal_SKK isNormal_SKS) (by decide)⟩

end FormalComputation.SKI
