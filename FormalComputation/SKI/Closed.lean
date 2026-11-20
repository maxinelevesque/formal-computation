import FormalComputation.SKI.Probes

/-!
# SKI: probes read closed terms

The essay's observation reads outcomes only on closed terms: there, every variable in an
outcome was supplied by the probe. Open terms are compared through every closing
substitution: two terms are the same under probes when all their closed instances are
(`ProbeEqCl`).

The permissive `ProbeEq` of `Probes.lean` reads any outcome written in variables alone,
including the term's own variables, and is not stable under substitution:
`a I` and `a K` agree under it (`probeEq_aI_aK`), while `I I` and `I K` do not
(`not_probeEq_II_IK`).

Checked here:

* substitution commutes with steps, runs and conversion (`Step.subst`, `reds_subst`,
  `conv_subst`), and with putting a term in a probe (`Probe.subst_plug`);
* sameness after running implies `ProbeEqCl` (`probeEqCl_of_conv`); on closed terms
  `ProbeEqCl` is `ProbeEq` (`probeEqCl_iff_of_closed`); `ProbeEqCl` is stable under every
  substitution (`probeEqCl_subst`), is an equivalence relation and a congruence
  (`probeEqCl_equivalence`, `probeEqCl_plug`);
* the two examples of the essay: a variable `a` is not the loop `Ω`
  (`not_probeEqCl_var_loop`: `Ω x` reads nothing, `not_reads_Ω_app`), and `a I` is not
  `a K` (`not_probeEqCl_aI_aK`).
-/

namespace FormalComputation.SKI

open Relation

/-! ### Substitution -/

/-- Substitute `σ n` for every `var n`. -/
def Tm.subst (σ : ℕ → Tm) : Tm → Tm
  | .S => .S
  | .K => .K
  | .I => .I
  | .var n => σ n
  | .app t u => Tm.subst σ t ⬝ Tm.subst σ u

/-- A **closed** term: no `var` occurs in it. -/
inductive Tm.Closed : Tm → Prop
  | S : Tm.Closed .S
  | K : Tm.Closed .K
  | I : Tm.Closed .I
  | app {t u : Tm} : Tm.Closed t → Tm.Closed u → Tm.Closed (t ⬝ u)

/-- Substitution fixes closed terms. -/
theorem Tm.subst_closed (σ : ℕ → Tm) {t : Tm} (h : t.Closed) : t.subst σ = t := by
  induction h with
  | S => rfl
  | K => rfl
  | I => rfl
  | app _ _ ih₁ ih₂ => simp only [Tm.subst, ih₁, ih₂]

/-- A closing substitution makes every term closed. -/
theorem Tm.closed_subst {σ : ℕ → Tm} (hσ : ∀ n, (σ n).Closed) (t : Tm) : (t.subst σ).Closed := by
  induction t with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | var n => exact hσ n
  | app t u ih₁ ih₂ => exact .app ih₁ ih₂

theorem Tm.subst_subst (σ τ : ℕ → Tm) (t : Tm) :
    (t.subst τ).subst σ = t.subst (fun n => (τ n).subst σ) := by
  induction t with
  | S => rfl
  | K => rfl
  | I => rfl
  | var n => rfl
  | app t u ih₁ ih₂ => simp only [Tm.subst, ih₁, ih₂]

/-- **A step survives substitution.** -/
def Step.subst (σ : ℕ → Tm) : {t u : Tm} → Step t u → Step (t.subst σ) (u.subst σ)
  | _, _, .i x => .i (x.subst σ)
  | _, _, .k x y => .k (x.subst σ) (y.subst σ)
  | _, _, .s x y z => .s (x.subst σ) (y.subst σ) (z.subst σ)
  | _, _, .appL u s => .appL (u.subst σ) (Step.subst σ s)
  | _, _, .appR t s => .appR (t.subst σ) (Step.subst σ s)

theorem reds_subst (σ : ℕ → Tm) {t u : Tm} (h : Reds t u) : Reds (t.subst σ) (u.subst σ) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨Step.subst σ hs.some⟩

theorem conv_subst (σ : ℕ → Tm) {t u : Tm} (h : Conv t u) : Conv (t.subst σ) (u.subst σ) := by
  induction h with
  | rel x y h => exact EqvGen.rel _ _ ⟨Step.subst σ h.some⟩
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

/-- Substitute inside the literals of a probe. -/
def Probe.substProbe (σ : ℕ → Tm) : Probe → Probe
  | .hole => .hole
  | .lit u => .lit (u.subst σ)
  | .app C D => .app (C.substProbe σ) (D.substProbe σ)

theorem Probe.subst_plug (σ : ℕ → Tm) (C : Probe) (t : Tm) :
    (C.plug t).subst σ = (C.substProbe σ).plug (t.subst σ) := by
  induction C with
  | hole => rfl
  | lit u => rfl
  | app C D ih₁ ih₂ => simp only [Probe.plug, Probe.substProbe, Tm.subst, ih₁, ih₂]

/-! ### Sameness under probes, read on closed instances -/

/-- **Sameness under every probe, read on closed terms**: all closed instances of `t` and `u`
are the same under every probe. A substituted term is closed, so every variable in a
reading comes from the probe. -/
def ProbeEqCl (t u : Tm) : Prop :=
  ∀ σ : ℕ → Tm, (∀ n, (σ n).Closed) → ProbeEq (t.subst σ) (u.subst σ)

theorem ProbeEqCl.refl (t : Tm) : ProbeEqCl t t := fun σ _ => ProbeEq.refl (t.subst σ)
theorem ProbeEqCl.symm {t u : Tm} (h : ProbeEqCl t u) : ProbeEqCl u t :=
  fun σ hσ => (h σ hσ).symm
theorem ProbeEqCl.trans {t u v : Tm} (h₁ : ProbeEqCl t u) (h₂ : ProbeEqCl u v) :
    ProbeEqCl t v := fun σ hσ => (h₁ σ hσ).trans (h₂ σ hσ)

theorem probeEqCl_equivalence : Equivalence ProbeEqCl :=
  ⟨ProbeEqCl.refl, ProbeEqCl.symm, ProbeEqCl.trans⟩

/-- **Sameness after running implies sameness under probes on closed instances.** -/
theorem probeEqCl_of_conv {t u : Tm} (h : Conv t u) : ProbeEqCl t u :=
  fun σ _ => probeEq_of_conv (conv_subst σ h)

/-- **On closed terms, the two readings agree.** -/
theorem probeEqCl_iff_of_closed {t u : Tm} (ht : t.Closed) (hu : u.Closed) :
    ProbeEqCl t u ↔ ProbeEq t u := by
  constructor
  · intro h
    have h' := h (fun _ => Tm.I) (fun _ => Tm.Closed.I)
    rwa [Tm.subst_closed _ ht, Tm.subst_closed _ hu] at h'
  · intro h σ _
    rw [Tm.subst_closed _ ht, Tm.subst_closed _ hu]
    exact h

/-- **`ProbeEqCl` is stable under every substitution**, closing or not. -/
theorem probeEqCl_subst {t u : Tm} (h : ProbeEqCl t u) (τ : ℕ → Tm) :
    ProbeEqCl (t.subst τ) (u.subst τ) := fun σ hσ => by
  rw [Tm.subst_subst, Tm.subst_subst]
  exact h _ fun n => Tm.closed_subst hσ (τ n)

/-- **`ProbeEqCl` is a congruence.** -/
theorem probeEqCl_plug {t u : Tm} (h : ProbeEqCl t u) (D : Probe) :
    ProbeEqCl (D.plug t) (D.plug u) := fun σ hσ => by
  rw [Probe.subst_plug, Probe.subst_plug]
  exact probeEq_plug (h σ hσ) _

/-! ### A variable is not the loop

Every reduct of `Ω x` has the form `A B x'`, where `A` and `B` are `S I I` under some `I`s.
Such a term contains a constant in head position, so it is never written in variables
alone: `Ω x` reads nothing. -/

/-- `S I I` under some number of `I`s. -/
inductive WSII : Tm → Prop
  | base : WSII (.S ⬝ .I ⬝ .I)
  | wrap {a : Tm} : WSII a → WSII (.I ⬝ a)

/-- The reducts of `Ω`: `A B` with `A`, `B` both `S I I` under some `I`s. -/
inductive OmegaRed : Tm → Prop
  | mk {a b : Tm} : WSII a → WSII b → OmegaRed (a ⬝ b)

theorem omegaRed_Ω : OmegaRed Ω := .mk .base .base

theorem wsii_step {a : Tm} (h : WSII a) : ∀ {a' : Tm}, Step a a' → WSII a' := by
  induction h with
  | base => intro a' s; exact (isNormal_of_hasRedex (t := .S ⬝ .I ⬝ .I) rfl _ s).elim
  | wrap h ih =>
    intro a' s
    cases s with
    | i => exact h
    | appL _ s => cases s
    | appR _ s => exact .wrap (ih s)

theorem omegaRed_step {m : Tm} (hm : OmegaRed m) : ∀ {m' : Tm}, Step m m' → OmegaRed m' := by
  intro m' s
  cases hm with
  | mk ha hb =>
    cases s with
    | i => cases ha
    | k => cases ha
    | s => cases ha with | base => exact .mk (.wrap hb) (.wrap hb)
    | appL _ s => exact .mk (wsii_step ha s) hb
    | appR _ s => exact .mk ha (wsii_step hb s)

theorem omega_app_step {m x : Tm} (hm : OmegaRed m) {t : Tm} (s : Step (m ⬝ x) t) :
    ∃ m' x', t = m' ⬝ x' ∧ OmegaRed m' ∧ Reds x x' := by
  cases hm with
  | mk ha hb =>
    cases s with
    | k => cases ha
    | s => cases ha
    | appL _ s => exact ⟨_, _, rfl, omegaRed_step (.mk ha hb) s, .refl⟩
    | appR _ s => exact ⟨_, _, rfl, .mk ha hb, .single ⟨s⟩⟩

theorem omega_app_reds {m x : Tm} (hm : OmegaRed m) {t : Tm} (h : Reds (m ⬝ x) t) :
    ∃ m' x', t = m' ⬝ x' ∧ OmegaRed m' ∧ Reds x x' := by
  induction h with
  | refl => exact ⟨m, x, rfl, hm, .refl⟩
  | tail _ hs ih =>
    obtain ⟨m₁, x₁, rfl, hm₁, hx₁⟩ := ih
    obtain ⟨m₂, x₂, rfl, hm₂, hx₂⟩ := omega_app_step hm₁ hs.some
    exact ⟨m₂, x₂, rfl, hm₂, hx₁.trans hx₂⟩

theorem not_inVars_wsii {a : Tm} (h : WSII a) : ¬ InVars a := by
  intro hv
  cases h with
  | base => cases hv with | app h₁ _ => cases h₁ with | app h₂ _ => cases h₂
  | wrap _ => cases hv with | app h₁ _ => cases h₁

theorem not_inVars_omegaRed_app {m x : Tm} (hm : OmegaRed m) : ¬ InVars (m ⬝ x) := by
  intro hv
  cases hm with
  | mk ha _ =>
    cases hv with
    | app h₁ _ => cases h₁ with | app h₂ _ => exact not_inVars_wsii ha h₂

/-- **`Ω x` reads nothing**, whatever `x` is. -/
theorem not_reads_Ω_app (x r : Tm) : ¬ Reads (Ω ⬝ x) r := by
  rintro ⟨hr, hv⟩
  obtain ⟨m', x', rfl, hm', -⟩ := omega_app_reds omegaRed_Ω hr
  exact not_inVars_omegaRed_app hm' hv

/-- The probe `[ ] x`, with `x = var 0`. -/
def probeX : Probe := .app .hole (.lit (.var 0))

theorem not_probeEq_I_Ω : ¬ ProbeEq .I Ω := fun h =>
  not_reads_Ω_app (.var 0) (.var 0) ((h probeX (.var 0)).1 ⟨.single ⟨Step.i _⟩, .var 0⟩)

theorem closed_Ω : Ω.Closed := .app (.app (.app .S .I) .I) (.app (.app .S .I) .I)

/-- **A variable is not the loop.** Substitute `I` for `a`: the probe `[ ] x` reads `x` from
`I x` and nothing from `Ω x`. -/
theorem not_probeEqCl_var_loop : ¬ ProbeEqCl (.var 0) Ω := fun h => by
  have h' := h (fun _ => Tm.I) (fun _ => Tm.Closed.I)
  rw [Tm.subst_closed _ closed_Ω] at h'
  exact not_probeEq_I_Ω h'

/-! ### `a I` and `a K` -/

theorem reads_II_xy : Reads (probeXY.plug (.I ⬝ .I)) (.var 0 ⬝ .var 1) :=
  ⟨(ReflTransGen.single ⟨Step.appL (.var 1) (Step.appL (.var 0) (Step.i .I))⟩).tail
    ⟨Step.appL (.var 1) (Step.i (.var 0))⟩, .app (.var 0) (.var 1)⟩

theorem reads_IK_xy : Reads (probeXY.plug (.I ⬝ .K)) (.var 0) :=
  ⟨(ReflTransGen.single ⟨Step.appL (.var 1) (Step.appL (.var 0) (Step.i .K))⟩).tail
    ⟨Step.k (.var 0) (.var 1)⟩, .var 0⟩

/-- `I I` and `I K` are told apart by the probe `[ ] x y`: it reads `x y` from one and `x`
from the other. -/
theorem not_probeEq_II_IK : ¬ ProbeEq (.I ⬝ .I) (.I ⬝ .K) := fun h =>
  absurd (reads_unique ((h probeXY _).1 reads_II_xy) reads_IK_xy) (by decide)

/-- **`a I` and `a K` are not the same under probes on closed instances**: substitute `I`
for `a`. -/
theorem not_probeEqCl_aI_aK : ¬ ProbeEqCl (.var 0 ⬝ .I) (.var 0 ⬝ .K) := fun h =>
  not_probeEq_II_IK (h (fun _ => Tm.I) (fun _ => Tm.Closed.I))

/-! ### The permissive reading identifies `a I` and `a K`

`Swap n a b t t'`: `t'` is `t` with some occurrences of `var n ⬝ a` replaced by `var n ⬝ b`.
When `a` is normal, `var n ⬝ a` is never contracted and has no step inside, so every step on
one side is matched by exactly one step on the other. When `a` and `b` are not written in
variables alone, neither is any term containing them, so readings are related only to
themselves. -/

/-- `t'` is `t` with some occurrences of `var n ⬝ a` replaced by `var n ⬝ b`. -/
inductive Swap (n : ℕ) (a b : Tm) : Tm → Tm → Prop
  | var (m : ℕ) : Swap n a b (.var m) (.var m)
  | S : Swap n a b .S .S
  | K : Swap n a b .K .K
  | I : Swap n a b .I .I
  | app {t t' u u' : Tm} : Swap n a b t t' → Swap n a b u u' → Swap n a b (t ⬝ u) (t' ⬝ u')
  | swap : Swap n a b (.var n ⬝ a) (.var n ⬝ b)

theorem Swap.refl {n : ℕ} {a b : Tm} : ∀ t : Tm, Swap n a b t t
  | .S => .S
  | .K => .K
  | .I => .I
  | .var m => .var m
  | .app t u => .app (Swap.refl t) (Swap.refl u)

theorem Swap.flip {n : ℕ} {a b t t' : Tm} (h : Swap n a b t t') : Swap n b a t' t := by
  induction h with
  | var m => exact .var m
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | swap => exact .swap

theorem swap_step {n : ℕ} {a b : Tm} (ha : IsNormal a) {t u : Tm} (s : Step t u) :
    ∀ {t' : Tm}, Swap n a b t t' → ∃ u', R1 t' u' ∧ Swap n a b u u' := by
  induction s with
  | i x =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      cases h₁
      exact ⟨_, ⟨Step.i _⟩, h₂⟩
  | k x y =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | app h₃ h₄ =>
        cases h₃
        exact ⟨_, ⟨Step.k _ _⟩, h₄⟩
  | s x y z =>
    intro t' h
    cases h with
    | app h₁ hz =>
      cases h₁ with
      | app h₃ hy =>
        cases h₃ with
        | app h₅ hx =>
          cases h₅
          exact ⟨_, ⟨Step.s _ _ _⟩, .app (.app hx hz) (.app hy hz)⟩
  | appL u st ih =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₁
      exact ⟨_, ⟨Step.appL _ hv.some⟩, .app hs h₂⟩
    | swap => cases st
  | appR t st ih =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₂
      exact ⟨_, ⟨Step.appR _ hv.some⟩, .app h₁ hs⟩
    | swap => exact (ha _ st).elim

theorem swap_reds {n : ℕ} {a b : Tm} (ha : IsNormal a) {t u : Tm} (h : Reds t u) :
    ∀ {t' : Tm}, Swap n a b t t' → ∃ u', Reds t' u' ∧ Swap n a b u u' := by
  induction h with
  | refl => intro t' h; exact ⟨t', .refl, h⟩
  | tail _ hs ih =>
    intro t' h
    obtain ⟨v, hv, hsv⟩ := ih h
    obtain ⟨w, hw, hsw⟩ := swap_step ha hs.some hsv
    exact ⟨w, hv.tail hw, hsw⟩

theorem swap_plug {n : ℕ} {a b : Tm} (C : Probe) {t t' : Tm} (h : Swap n a b t t') :
    Swap n a b (C.plug t) (C.plug t') := by
  induction C with
  | hole => exact h
  | lit u => exact Swap.refl u
  | app C D ih₁ ih₂ => exact .app ih₁ ih₂

theorem swap_inVars {n : ℕ} {a b : Tm} (ha : ¬ InVars a) {t t' : Tm} (h : Swap n a b t t') :
    InVars t → t' = t := by
  induction h with
  | var m => intro _; rfl
  | S => intro hp; cases hp
  | K => intro hp; cases hp
  | I => intro hp; cases hp
  | app _ _ ih₁ ih₂ =>
    intro hp
    cases hp with
    | app h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]
  | swap => intro hp; cases hp with | app _ h₂ => exact (ha h₂).elim

theorem probeEq_of_swap {n : ℕ} {a b : Tm} (ha : IsNormal a) (hb : IsNormal b)
    (ha' : ¬ InVars a) (hb' : ¬ InVars b) {t t' : Tm} (h : Swap n a b t t') : ProbeEq t t' := by
  intro C r
  constructor
  · rintro ⟨hr, hp⟩
    obtain ⟨u', hu', hs⟩ := swap_reds ha hr (swap_plug C h)
    rw [swap_inVars ha' hs hp] at hu'
    exact ⟨hu', hp⟩
  · rintro ⟨hr, hp⟩
    obtain ⟨u, hu, hs⟩ := swap_reds hb hr (swap_plug C h).flip
    rw [swap_inVars hb' hs hp] at hu
    exact ⟨hu, hp⟩

/-- **The permissive reading identifies `a I` and `a K`.** -/
theorem probeEq_aI_aK : ProbeEq (.var 0 ⬝ .I) (.var 0 ⬝ .K) :=
  probeEq_of_swap (n := 0) isNormal_I isNormal_K (fun h => by cases h) (fun h => by cases h) .swap

/-- **The permissive reading is not stable under substitution**: it identifies `a I` and `a K`
but not their instances `I I` and `I K`; reading closed instances keeps them apart. -/
theorem probeEq_not_subst_stable :
    ProbeEq (.var 0 ⬝ .I) (.var 0 ⬝ .K) ∧ ¬ ProbeEq (.I ⬝ .I) (.I ⬝ .K) ∧
      ¬ ProbeEqCl (.var 0 ⬝ .I) (.var 0 ⬝ .K) :=
  ⟨probeEq_aI_aK, not_probeEq_II_IK, not_probeEqCl_aI_aK⟩

end FormalComputation.SKI
