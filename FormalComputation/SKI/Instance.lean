import FormalComputation.SKI.Probes
import FormalComputation.Calculus

/-!
# SKI as an instance of the general calculus with probes

Combinatory logic with the essay's probes is a `Calculus`. Its probes are multi-hole contexts,
and its outcomes are terms written in variables alone. It is confluent. The general notions
agree with the SKI ones by definition (`calculus_probeEq_iff`, `calculus_conv_iff`), so every
general theorem of `FormalComputation.Calculus` applies to SKI.
-/

namespace FormalComputation.SKI

open Relation

/-- **SKI with the essay's probes, as a calculus.** -/
def calculus : Calculus where
  Tm := Tm
  Step t u := Nonempty (Step t u)
  Ctx := Probe
  hole := .hole
  plug := Probe.plug
  subst := Probe.subst
  plug_hole _ := rfl
  plug_subst := Probe.plug_subst
  reds_plug C _ _ h := reds_plug_of_step C h.some
  Out := InVars
  out_normal hr h := isNormal_of_inVars hr _ h.some

/-- SKI is confluent, as a calculus. -/
theorem calculus_confluent : calculus.Confluent := fun _ _ _ hb hc => confluent hb hc

/-- The general sameness under probes is the essay's. -/
theorem calculus_probeEq_iff {t u : Tm} : calculus.ProbeEq t u ↔ ProbeEq t u := Iff.rfl

/-- The general sameness after running is the essay's. -/
theorem calculus_conv_iff {t u : Tm} : calculus.Conv t u ↔ Conv t u := Iff.rfl

/-- Normal forms are the same in both formulations. -/
theorem calculus_isNormal_iff {t : Tm} : calculus.IsNormal t ↔ IsNormal t :=
  ⟨fun h u s => h u ⟨s⟩, fun h u s => h u s.some⟩

/-- The general sameness under probes that read code is the essay's. -/
theorem calculus_codeEq_iff {t u : Tm} : calculus.CodeEq t u ↔ CodeEq t u :=
  forall_congr' fun _ => forall_congr' fun _ =>
    iff_congr (and_congr Iff.rfl calculus_isNormal_iff) (and_congr Iff.rfl calculus_isNormal_iff)

/-- For example, the general theorem gives back `probeEq_of_conv` for SKI. -/
example {t u : Tm} (h : Conv t u) : ProbeEq t u :=
  calculus.probeEq_of_conv calculus_confluent h

end FormalComputation.SKI
