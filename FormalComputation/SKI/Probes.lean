import FormalComputation.SKI.Confluence

/-!
# SKI: probes and sameness under probes (the essay "Atoms and Probes")

A **probe** is a context: a term with holes (any number, so "however elaborate"). The term
under test is put in every hole and the result is run. The probe **reads** an outcome only
if the run reaches a term written in variables alone: it may read only what it supplied
(`Reads`). Two terms are the **same under every probe** when every probe reads the same
outcomes from both (`ProbeEq`).

Checked here, in the essay's order:

* sameness after running implies sameness under probes (`probeEq_of_conv`), which needs
  confluence; the converse fails (`probes_not_running`);
* sameness under probes is a congruence (`probeEq_plug`);
* the table of six terms: `I`, `S K K`, `S K S` agree under every probe, and so do `K I`
  and `K (S K K)`, while the three groups are separated by the probe `[ ] x y`
  (`six_terms`). More generally `S K y` and `I` agree under every probe for every `y`
  (`probeEq_SK`), which is the sense in which the rule `S K y → I` is sound;
* a predicate defined by a probe is a type, and respects sameness under probes; "runs to
  `I`" is a type that no probe defines (`runsToI_not_probe`);
* when probes may read code (`ReadsCode`, any normal form), sameness under probes is
  conversion for terms that have a value (`codeEq_iff_conv`), and it separates `I` from
  `S K K` (`not_codeEq_I_SKK`), while `I a` and `a` still agree (`codeEq_Ia_a`).

The simulation `Sim` behind `probeEq_SK` replaces occurrences of `I` by `S K y`. Each step on
either side is matched by zero or more steps on the other, and terms written in variables
alone are related only to themselves.
-/

namespace FormalComputation.SKI

open Relation

/-- Terms written in variables alone: what a probe may read. -/
inductive InVars : Tm → Prop
  | var (n : ℕ) : InVars (.var n)
  | app {t u : Tm} : InVars t → InVars u → InVars (t ⬝ u)

theorem not_inVars_of_step {t u : Tm} (s : Step t u) : ¬ InVars t := by
  induction s with
  | i x => intro h; cases h with | app h₁ _ => cases h₁
  | k x y => intro h; cases h with | app h₁ _ => cases h₁ with | app h₂ _ => cases h₂
  | s x y z =>
    intro h
    cases h with | app h₁ _ => cases h₁ with | app h₂ _ => cases h₂ with | app h₃ _ => cases h₃
  | appL u _ ih => intro h; cases h with | app h₁ _ => exact ih h₁
  | appR t _ ih => intro h; cases h with | app _ h₂ => exact ih h₂

theorem isNormal_of_inVars {t : Tm} (h : InVars t) : IsNormal t :=
  fun _ s => not_inVars_of_step s h

/-- A **probe**: a context with any number of holes. -/
inductive Probe
  | hole
  | lit (t : Tm)
  | app (C D : Probe)

/-- Put the term under test in every hole. -/
def Probe.plug : Probe → Tm → Tm
  | .hole, t => t
  | .lit u, _ => u
  | .app C D, t => C.plug t ⬝ D.plug t

/-- Put the probe `D` in every hole of `C`. -/
def Probe.subst : Probe → Probe → Probe
  | .hole, D => D
  | .lit u, _ => .lit u
  | .app C₁ C₂, D => .app (C₁.subst D) (C₂.subst D)

theorem Probe.plug_subst (C D : Probe) (t : Tm) : (C.subst D).plug t = C.plug (D.plug t) := by
  induction C with
  | hole => rfl
  | lit u => rfl
  | app C₁ C₂ ih₁ ih₂ => simp only [Probe.subst, Probe.plug, ih₁, ih₂]

/-- The probe **reads** `r` from `t`: `t` runs to `r`, written in variables alone. -/
def Reads (t r : Tm) : Prop := Reds t r ∧ InVars r

/-- **Sameness under every probe.** -/
def ProbeEq (t u : Tm) : Prop := ∀ (C : Probe) (r : Tm), Reads (C.plug t) r ↔ Reads (C.plug u) r

theorem ProbeEq.refl (t : Tm) : ProbeEq t t := fun _ _ => Iff.rfl
theorem ProbeEq.symm {t u : Tm} (h : ProbeEq t u) : ProbeEq u t := fun C r => (h C r).symm
theorem ProbeEq.trans {t u v : Tm} (h₁ : ProbeEq t u) (h₂ : ProbeEq u v) : ProbeEq t v :=
  fun C r => (h₁ C r).trans (h₂ C r)

/-- **Sameness under probes is a congruence.** -/
theorem probeEq_plug {t u : Tm} (h : ProbeEq t u) (D : Probe) :
    ProbeEq (D.plug t) (D.plug u) := fun C r => by
  rw [← Probe.plug_subst, ← Probe.plug_subst]
  exact h (C.subst D) r

/-- A probe reads at most one outcome. -/
theorem reads_unique {t r r' : Tm} (h : Reads t r) (h' : Reads t r') : r = r' :=
  conv_normal_eq (EqvGen.trans _ _ _ (EqvGen.symm _ _ (reds_conv h.1)) (reds_conv h'.1))
    (isNormal_of_inVars h.2) (isNormal_of_inVars h'.2)

/-! ### Running implies probes -/

theorem reds_plug_of_step (C : Probe) {t u : Tm} (s : Step t u) :
    Reds (C.plug t) (C.plug u) := by
  induction C with
  | hole => exact .single ⟨s⟩
  | lit v => exact .refl
  | app C D ih₁ ih₂ => exact reds_app ih₁ ih₂

theorem conv_plug (C : Probe) {t u : Tm} (h : Conv t u) : Conv (C.plug t) (C.plug u) := by
  induction h with
  | rel x y h => exact reds_conv (reds_plug_of_step C h.some)
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact EqvGen.trans _ _ _ ih₁ ih₂

theorem reads_of_conv {a b r : Tm} (h : Conv a b) (hr : Reads a r) : Reads b r :=
  ⟨reds_of_conv_normal (EqvGen.trans _ _ _ (EqvGen.symm _ _ h) (reds_conv hr.1))
    (isNormal_of_inVars hr.2), hr.2⟩

/-- **Sameness after running implies sameness under probes.** The proof uses confluence. -/
theorem probeEq_of_conv {t u : Tm} (h : Conv t u) : ProbeEq t u := fun C _ =>
  ⟨reads_of_conv (conv_plug C h), reads_of_conv (EqvGen.symm _ _ (conv_plug C h))⟩

/-! ### The simulation: `I` against `S K y` -/

/-- `Sim t t'`: `t'` is `t` with some occurrences of `I` replaced by `S K y` (for various `y`),
together with the intermediate state `K x' y` of a replaced `I x` that has taken one step. -/
inductive Sim : Tm → Tm → Prop
  | var (n : ℕ) : Sim (.var n) (.var n)
  | S : Sim .S .S
  | K : Sim .K .K
  | I : Sim .I .I
  | sk (y : Tm) : Sim .I (.S ⬝ .K ⬝ y)
  | app {t t' u u' : Tm} : Sim t t' → Sim u u' → Sim (t ⬝ u) (t' ⬝ u')
  | tail {x x' : Tm} (y : Tm) : Sim x x' → Sim (.I ⬝ x) (.K ⬝ x' ⬝ y)

theorem Sim.refl : ∀ t : Tm, Sim t t
  | .S => .S
  | .K => .K
  | .I => .I
  | .var n => .var n
  | .app t u => .app (Sim.refl t) (Sim.refl u)

theorem step_K_inv {x w : Tm} (s : Step (.K ⬝ x) w) :
    ∃ x', w = .K ⬝ x' ∧ Nonempty (Step x x') := by
  cases s with
  | appL _ s => cases s
  | appR _ s => exact ⟨_, rfl, ⟨s⟩⟩

theorem reds_K_inv {x w : Tm} (h : Reds (.K ⬝ x) w) : ∃ x', w = .K ⬝ x' ∧ Reds x x' := by
  induction h with
  | refl => exact ⟨x, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨x₁, rfl, h₁⟩ := ih
    obtain ⟨x₂, rfl, ⟨s₂⟩⟩ := step_K_inv hs.some
    exact ⟨x₂, rfl, h₁.tail ⟨s₂⟩⟩

/-- Every step on the `I` side is matched on the other side. -/
theorem sim_forward {t u : Tm} (s : Step t u) :
    ∀ {t' : Tm}, Sim t t' → ∃ u', Reds t' u' ∧ Sim u u' := by
  induction s with
  | i x =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | I => exact ⟨_, .single ⟨Step.i _⟩, h₂⟩
      | sk y => exact ⟨_, (ReflTransGen.single ⟨Step.s .K y _⟩).tail ⟨Step.k _ _⟩, h₂⟩
    | tail y h₂ => exact ⟨_, .single ⟨Step.k _ y⟩, h₂⟩
  | k x y =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | app h₃ h₄ =>
        cases h₃
        exact ⟨_, .single ⟨Step.k _ _⟩, h₄⟩
  | s x y z =>
    intro t' h
    cases h with
    | app h₁ hz =>
      cases h₁ with
      | app h₃ hy =>
        cases h₃ with
        | app h₅ hx =>
          cases h₅
          exact ⟨_, .single ⟨Step.s _ _ _⟩, .app (.app hx hz) (.app hy hz)⟩
  | appL u st ih =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₁
      exact ⟨_, reds_appL _ hv, .app hs h₂⟩
    | tail y h₂ => cases st
  | appR t st ih =>
    intro t' h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₂
      exact ⟨_, reds_appR _ hv, .app h₁ hs⟩
    | tail y h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₂
      exact ⟨_, reds_appL y (reds_appR .K hv), .tail y hs⟩

/-- Every step on the replaced side is matched by zero or more steps on the `I` side. -/
theorem sim_backward {t' u' : Tm} (s : Step t' u') :
    ∀ {t : Tm}, Sim t t' → ∃ u, Reds t u ∧ Sim u u' := by
  induction s with
  | i x' =>
    intro t h
    cases h with
    | app h₁ h₂ =>
      cases h₁
      exact ⟨_, .single ⟨Step.i _⟩, h₂⟩
  | k x' y' =>
    intro t h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | app h₃ h₄ =>
        cases h₃
        exact ⟨_, .single ⟨Step.k _ _⟩, h₄⟩
    | tail y h₂ => exact ⟨_, .single ⟨Step.i _⟩, h₂⟩
  | s x' y' z' =>
    intro t h
    cases h with
    | app h₁ hz =>
      cases h₁ with
      | app h₃ hy =>
        cases h₃ with
        | app h₅ hx =>
          cases h₅
          exact ⟨_, .single ⟨Step.s _ _ _⟩, .app (.app hx hz) (.app hy hz)⟩
      | sk y => exact ⟨_, .refl, .tail _ hz⟩
  | appL u' st ih =>
    intro t h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₁
      exact ⟨_, reds_appL _ hv, .app hs h₂⟩
    | sk y =>
      cases st with
      | appL _ s₀ => cases s₀
      | appR _ s₀ => cases s₀
    | tail y hx =>
      obtain ⟨u₀, hu₀, hs₀⟩ := ih (Sim.app Sim.K hx)
      obtain ⟨x'', rfl, -⟩ := step_K_inv st
      cases hs₀ with
      | app h₃ h₄ =>
        cases h₃
        obtain ⟨x₁, hx₁, hr⟩ := reds_K_inv hu₀
        cases hx₁
        exact ⟨_, reds_appR .I hr, .tail _ h₄⟩
  | appR f' st ih =>
    intro t h
    cases h with
    | app h₁ h₂ =>
      obtain ⟨v, hv, hs⟩ := ih h₂
      exact ⟨_, reds_appR _ hv, .app h₁ hs⟩
    | sk y => exact ⟨_, .refl, .sk _⟩
    | tail y hx => exact ⟨_, .refl, .tail _ hx⟩

theorem sim_forward_reds {t u : Tm} (h : Reds t u) :
    ∀ {t' : Tm}, Sim t t' → ∃ u', Reds t' u' ∧ Sim u u' := by
  induction h with
  | refl => intro t' h; exact ⟨t', .refl, h⟩
  | tail _ hs ih =>
    intro t' h
    obtain ⟨v, hv, hsv⟩ := ih h
    obtain ⟨w, hw, hsw⟩ := sim_forward hs.some hsv
    exact ⟨w, hv.trans hw, hsw⟩

theorem sim_backward_reds {t' u' : Tm} (h : Reds t' u') :
    ∀ {t : Tm}, Sim t t' → ∃ u, Reds t u ∧ Sim u u' := by
  induction h with
  | refl => intro t h; exact ⟨t, .refl, h⟩
  | tail _ hs ih =>
    intro t h
    obtain ⟨v, hv, hsv⟩ := ih h
    obtain ⟨w, hw, hsw⟩ := sim_backward hs.some hsv
    exact ⟨w, hv.trans hw, hsw⟩

theorem sim_plug (C : Probe) {t t' : Tm} (h : Sim t t') : Sim (C.plug t) (C.plug t') := by
  induction C with
  | hole => exact h
  | lit u => exact Sim.refl u
  | app C D ih₁ ih₂ => exact .app ih₁ ih₂

theorem sim_inVars_left {t t' : Tm} (h : Sim t t') : InVars t → t' = t := by
  induction h with
  | var n => intro _; rfl
  | S => intro hp; cases hp
  | K => intro hp; cases hp
  | I => intro hp; cases hp
  | sk y => intro hp; cases hp
  | app _ _ ih₁ ih₂ =>
    intro hp
    cases hp with
    | app h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]
  | tail y _ _ => intro hp; cases hp with | app h₁ _ => cases h₁

theorem sim_inVars_right {t t' : Tm} (h : Sim t t') : InVars t' → t = t' := by
  induction h with
  | var n => intro _; rfl
  | S => intro hp; cases hp
  | K => intro hp; cases hp
  | I => intro hp; cases hp
  | sk y => intro hp; cases hp with | app h₁ _ => cases h₁ with | app h₂ _ => cases h₂
  | app _ _ ih₁ ih₂ =>
    intro hp
    cases hp with
    | app h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]
  | tail y _ _ => intro hp; cases hp with | app h₁ _ => cases h₁ with | app h₂ _ => cases h₂

/-- Related terms are the same under every probe. -/
theorem probeEq_of_sim {t t' : Tm} (h : Sim t t') : ProbeEq t t' := by
  intro C r
  have hC := sim_plug C h
  constructor
  · rintro ⟨hr, hp⟩
    obtain ⟨u', hu', hs⟩ := sim_forward_reds hr hC
    rw [sim_inVars_left hs hp] at hu'
    exact ⟨hu', hp⟩
  · rintro ⟨hr, hp⟩
    obtain ⟨u, hu, hs⟩ := sim_backward_reds hr hC
    rw [sim_inVars_right hs hp] at hu
    exact ⟨hu, hp⟩

/-- **The rule `S K y → I` is sound**: `S K y` and `I` are the same under every probe. -/
theorem probeEq_SK (y : Tm) : ProbeEq (.S ⬝ .K ⬝ y) .I := (probeEq_of_sim (Sim.sk y)).symm

/-! ### The table of six terms -/

/-- The probe `[ ] x y`, with `x = var 0` and `y = var 1`. -/
def probeXY : Probe := .app (.app .hole (.lit (.var 0))) (.lit (.var 1))

theorem reads_I_xy : Reads (probeXY.plug .I) (.var 0 ⬝ .var 1) :=
  ⟨.single ⟨Step.appL _ (Step.i _)⟩, .app (.var 0) (.var 1)⟩

theorem reads_K_xy : Reads (probeXY.plug .K) (.var 0) :=
  ⟨.single ⟨Step.k _ _⟩, .var 0⟩

theorem reads_KI_xy : Reads (probeXY.plug (.K ⬝ .I)) (.var 1) :=
  ⟨(ReflTransGen.single ⟨Step.appL _ (Step.k .I (.var 0))⟩).tail ⟨Step.i _⟩, .var 1⟩

/-- **The table of six terms.** `I`, `S K K`, `S K S` are the same under every probe, and so are
`K I` and `K (S K K)`; the three groups `{I, S K K, S K S}`, `{K I, K (S K K)}` and `{K}` are
told apart by the probe `[ ] x y`. -/
theorem six_terms :
    ProbeEq .I (.S ⬝ .K ⬝ .K) ∧ ProbeEq .I (.S ⬝ .K ⬝ .S) ∧
      ProbeEq (.K ⬝ .I) (.K ⬝ (.S ⬝ .K ⬝ .K)) ∧
      ¬ ProbeEq .I (.K ⬝ .I) ∧ ¬ ProbeEq .I .K ∧ ¬ ProbeEq (.K ⬝ .I) .K := by
  refine ⟨probeEq_of_sim (.sk _), probeEq_of_sim (.sk _), probeEq_of_sim (.app .K (.sk _)),
    fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (reads_unique ((h probeXY _).1 reads_I_xy) reads_KI_xy) (by decide)
  · exact absurd (reads_unique ((h probeXY _).1 reads_I_xy) reads_K_xy) (by decide)
  · exact absurd (reads_unique ((h probeXY _).1 reads_KI_xy) reads_K_xy) (by decide)

/-- **Running and probes come apart**: `I` and `S K K` are the same under every probe but lie
in different fibres. -/
theorem probes_not_running : ProbeEq .I (.S ⬝ .K ⬝ .K) ∧ ¬ Conv .I (.S ⬝ .K ⬝ .K) :=
  ⟨six_terms.1, three_fibres.1⟩

/-! ### Types defined by probes -/

/-- The predicate defined by a probe and a reading. -/
def ProbePred (C : Probe) (r : Tm) : Tm → Prop := fun t => Reads (C.plug t) r

/-- **A predicate defined by a probe is a type.** -/
theorem isType_probePred (C : Probe) (r : Tm) : IsType (ProbePred C r) :=
  isType_of_conv fun _ _ h =>
    ⟨reads_of_conv (conv_plug C h), reads_of_conv (EqvGen.symm _ _ (conv_plug C h))⟩

/-- A type defined by a probe cannot separate terms that probes cannot separate. -/
theorem probePred_respects {C : Probe} {r t u : Tm} (h : ProbeEq t u) :
    ProbePred C r t ↔ ProbePred C r u := h C r

/-- "Runs to `I`" is a type. -/
theorem isType_runsToI : IsType (fun t => Reds t .I) :=
  isType_of_conv fun _ _ h =>
    ⟨fun ht => reds_of_conv_normal
        (EqvGen.trans _ _ _ (EqvGen.symm _ _ h) (reds_conv ht)) isNormal_I,
     fun hu => reds_of_conv_normal (EqvGen.trans _ _ _ h (reds_conv hu)) isNormal_I⟩

/-- **"Runs to `I`" is a type that no probe defines.** -/
theorem runsToI_not_probe : ¬ ∃ (C : Probe) (r : Tm), ∀ t, Reds t .I ↔ ProbePred C r t := by
  rintro ⟨C, r, h⟩
  have hI : ProbePred C r .I := (h .I).1 .refl
  have hSKK : Reds (.S ⬝ .K ⬝ .K) .I := (h _).2 ((probePred_respects six_terms.1).1 hI)
  exact absurd (reds_normal isNormal_SKK hSKK) (by decide)

/-! ### Probes that read code -/

/-- A probe that may read code reads any normal form. -/
def ReadsCode (t r : Tm) : Prop := Reds t r ∧ IsNormal r

/-- Sameness under probes that may read code. -/
def CodeEq (t u : Tm) : Prop :=
  ∀ (C : Probe) (r : Tm), ReadsCode (C.plug t) r ↔ ReadsCode (C.plug u) r

theorem readsCode_of_conv {a b r : Tm} (h : Conv a b) (hr : ReadsCode a r) : ReadsCode b r :=
  ⟨reds_of_conv_normal (EqvGen.trans _ _ _ (EqvGen.symm _ _ h) (reds_conv hr.1)) hr.2, hr.2⟩

/-- Running implies sameness under probes that read code. -/
theorem codeEq_of_conv {t u : Tm} (h : Conv t u) : CodeEq t u := fun C _ =>
  ⟨readsCode_of_conv (conv_plug C h), readsCode_of_conv (EqvGen.symm _ _ (conv_plug C h))⟩

/-- **With probes that read code, sameness under probes is sameness after running**, for
terms that have a value. -/
theorem codeEq_iff_conv {t u : Tm} (ht : ∃ r, ReadsCode t r) : CodeEq t u ↔ Conv t u := by
  refine ⟨fun h => ?_, codeEq_of_conv⟩
  obtain ⟨r, hr⟩ := ht
  obtain ⟨hu, -⟩ := (h .hole r).1 hr
  exact EqvGen.trans _ _ _ (reds_conv hr.1) (EqvGen.symm _ _ (reds_conv hu))

/-- Probes that read code tell `I` from `S K K`. -/
theorem not_codeEq_I_SKK : ¬ CodeEq .I (.S ⬝ .K ⬝ .K) := fun h => by
  have h' := (h .hole .I).1 ⟨.refl, isNormal_I⟩
  exact absurd (reds_normal isNormal_SKK h'.1) (by decide)

/-- Still, `I a` and `a` agree: a step is invisible to a probe however much it can read. -/
theorem codeEq_Ia_a : CodeEq (.I ⬝ .var 0) (.var 0) :=
  codeEq_of_conv (EqvGen.rel _ _ ⟨Step.i _⟩)

end FormalComputation.SKI
