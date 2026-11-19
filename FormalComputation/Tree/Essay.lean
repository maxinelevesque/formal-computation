import FormalComputation.Tree.Calculus

/-!
# Tree calculus in the essay's figures (the calculus switch, `notes/15` §15.3)

The essay "Atoms and Probes" is written for combinatory logic. Its calculus switch shows each
figure in tree calculus too. This file checks the tree-calculus claims of that switch.

Abbreviations, as in the essay's legend: `△` is the leaf `L`, `K = △△`, and `S x y = △(△x)y`.
The three identities of the bench are `S K y` for `y = △, K, △K`:
`I = △(△K)△`, `I' = △(△K)K`, `I'' = △(△K)(△K)`.

Proved here:
- **The bench** (`tree_six_terms`): the six terms `I, I', I'', K I, K I', K` under the probes
  `[ ]`, `[ ] x`, `[ ] x y` read exactly what their SKI counterparts read; a fourth probe, the
  triage probe `triP`, reads `x`, `y`, `z` from the three identities and nothing from the
  other three terms. So in tree calculus all six terms are told apart by probes
  (`tree_six_distinct`), where SKI has three classes (`SKI.six_terms`).
- **The rule `S K y → I` is unsound for tree probes** (`sk_unsound`): the three identities are
  pairwise different under probes, so any step relation containing the rule relates terms that
  probes separate. In SKI the rule is sound (`SKI.probeEq_SK`).
- **Fundamental lemmas** (`fundamental_K`, `fundamental_S`, `fundamental_triage`): `K` is in
  `⟦A → B → A⟧` for every type `A`; `S x y` and triage respect types when their parts do.
- **The loop of `ω ω`** (`omega_cycle`): with `ω = S I I = △(△I)I`, `ω ω` runs back to itself
  in five steps.
-/

namespace FormalComputation.Tree

open Relation Tm

/-! ### Reading off a run -/

/-- Whether a term is written in variables alone, as a decidable test. -/
def varsOnly : Tm ℕ → Bool
  | L => false
  | V _ => true
  | f ∙ a => varsOnly f && varsOnly a

theorem varsOnly_of_inVars {t : Tm ℕ} (h : InVars t) : varsOnly t = true := by
  induction h with
  | var n => rfl
  | app _ _ ih₁ ih₂ => simp [varsOnly, ih₁, ih₂]

/-- A probe **reads nothing** from a term: the run reaches no outcome. -/
def ReadsNothing (t : Tm ℕ) : Prop := ∀ r, ¬ calculus.Reads t r

/-- If the certified evaluator reaches `r` and `r` is written in variables, `t` reads `r`. -/
theorem reads_of_run {t r : Tm ℕ} (n : ℕ) (h : (run n t).1 = r) (hr : InVars r) :
    calculus.Reads t r :=
  ⟨h ▸ (run n t).2, hr⟩

/-- If the certified evaluator reaches a normal form that is not written in variables, `t`
reads nothing: by confluence that normal form is the only one. -/
theorem readsNothing_of_run {t : Tm ℕ} (n : ℕ) (h₁ : hasRedex (run n t).1 = false)
    (h₂ : varsOnly (run n t).1 = false) : ReadsNothing t := by
  intro r hr
  have e : r = (run n t).1 :=
    Calculus.conv_normal_eq calculus_confluent
      (EqvGen.trans _ _ _ (EqvGen.symm _ _ (Calculus.reds_conv hr.1))
        (Calculus.reds_conv (L := calculus) (run n t).2))
      (Calculus.isNormal_of_out calculus_confluent hr.2) (isNormal_of_hasRedex h₁)
  have hv : InVars (run n t).1 := e ▸ hr.2
  exact absurd (h₂.symm.trans (varsOnly_of_inVars hv)) (by decide)

/-- A probe that reads two different outcomes from two terms separates them. -/
theorem not_probeEq_of_reads {t u r r' : Tm ℕ} (C : Probe ℕ) (h : calculus.Reads (C.plug t) r)
    (h' : calculus.Reads (C.plug u) r') (hne : r ≠ r') : ¬ calculus.ProbeEq t u :=
  fun hp => hne (Calculus.reads_unique calculus_confluent ((hp C r).1 h) h')

/-- A probe that reads an outcome from one term and nothing from another separates them. -/
theorem not_probeEq_of_reads_nothing {t u r : Tm ℕ} (C : Probe ℕ)
    (h : calculus.Reads (C.plug t) r) (h' : ReadsNothing (C.plug u)) :
    ¬ calculus.ProbeEq t u :=
  fun hp => h' r ((hp C r).1 h)

/-! ### The bench -/

/-- `S K (△K)`: a third identity. -/
def idT'' : Tm ℕ := L ∙ (L ∙ K) ∙ (L ∙ K)

/-- The probe `[ ] x`. -/
def probeX : Probe ℕ := .app .hole (.lit (V 0))

/-- The probe `[ ] x y`. -/
def probeXY : Probe ℕ := .app (.app .hole (.lit (V 0))) (.lit (V 1))

/-- Take the right child of a fork; send a leaf or a stem to the fork `△△△`. -/
def extract : Tm ℕ := triage (K ∙ L) (K ∙ (K ∙ L)) (K ∙ idT)

/-- Read a leaf as `x`, the stem `△△` as `y`, a stem `△(△ w)` as `z`; leave a fork as it is. -/
def readShape : Tm ℕ := triage (V 0) (triage (V 1) (K ∙ V 2) L) L

/-- **The triage probe**: triage on the right child of the code under test. -/
def triP : Probe ℕ := .app (.lit readShape) (.app (.lit extract) .hole)

/-- **The tree bench.** Rows: the probes `[ ]`, `[ ] x`, `[ ] x y` and the triage probe.
Columns: `I, I', I'', K I, K I', K`. Each cell states what the probe reads, or that it reads
nothing. The first three rows agree with SKI's (`SKI.six_terms`); the fourth row exists only
because tree calculus can triage on code. -/
theorem tree_six_terms :
    -- `[ ]`: nothing from any of the six
    (ReadsNothing (Probe.plug .hole idT) ∧ ReadsNothing (Probe.plug .hole idT') ∧
      ReadsNothing (Probe.plug .hole idT'') ∧ ReadsNothing (Probe.plug .hole (K ∙ idT)) ∧
      ReadsNothing (Probe.plug .hole (K ∙ idT')) ∧ ReadsNothing (Probe.plug .hole K)) ∧
    -- `[ ] x`: `x` from the identities, nothing from the others
    (calculus.Reads (probeX.plug idT) (V 0) ∧ calculus.Reads (probeX.plug idT') (V 0) ∧
      calculus.Reads (probeX.plug idT'') (V 0) ∧ ReadsNothing (probeX.plug (K ∙ idT)) ∧
      ReadsNothing (probeX.plug (K ∙ idT')) ∧ ReadsNothing (probeX.plug K)) ∧
    -- `[ ] x y`: `x y`, `x y`, `x y`, `y`, `y`, `x`
    (calculus.Reads (probeXY.plug idT) (V 0 ∙ V 1) ∧
      calculus.Reads (probeXY.plug idT') (V 0 ∙ V 1) ∧
      calculus.Reads (probeXY.plug idT'') (V 0 ∙ V 1) ∧
      calculus.Reads (probeXY.plug (K ∙ idT)) (V 1) ∧
      calculus.Reads (probeXY.plug (K ∙ idT')) (V 1) ∧ calculus.Reads (probeXY.plug K) (V 0)) ∧
    -- the triage probe: `x`, `y`, `z` from the identities, nothing from the others
    (calculus.Reads (triP.plug idT) (V 0) ∧ calculus.Reads (triP.plug idT') (V 1) ∧
      calculus.Reads (triP.plug idT'') (V 2) ∧ ReadsNothing (triP.plug (K ∙ idT)) ∧
      ReadsNothing (triP.plug (K ∙ idT')) ∧ ReadsNothing (triP.plug K)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- `[ ]`
  · exact readsNothing_of_run 1 (by decide) (by decide)
  · exact readsNothing_of_run 1 (by decide) (by decide)
  · exact readsNothing_of_run 1 (by decide) (by decide)
  · exact readsNothing_of_run 1 (by decide) (by decide)
  · exact readsNothing_of_run 1 (by decide) (by decide)
  · exact readsNothing_of_run 1 (by decide) (by decide)
  -- `[ ] x`
  · exact reads_of_run 10 (by decide) (.var 0)
  · exact reads_of_run 10 (by decide) (.var 0)
  · exact reads_of_run 10 (by decide) (.var 0)
  · exact readsNothing_of_run 10 (by decide) (by decide)
  · exact readsNothing_of_run 10 (by decide) (by decide)
  · exact readsNothing_of_run 10 (by decide) (by decide)
  -- `[ ] x y`
  · exact reads_of_run 10 (by decide) (.app (.var 0) (.var 1))
  · exact reads_of_run 10 (by decide) (.app (.var 0) (.var 1))
  · exact reads_of_run 10 (by decide) (.app (.var 0) (.var 1))
  · exact reads_of_run 10 (by decide) (.var 1)
  · exact reads_of_run 10 (by decide) (.var 1)
  · exact reads_of_run 10 (by decide) (.var 0)
  -- the triage probe
  · exact reads_of_run 20 (by decide) (.var 0)
  · exact reads_of_run 20 (by decide) (.var 1)
  · exact reads_of_run 20 (by decide) (.var 2)
  · exact readsNothing_of_run 20 (by decide) (by decide)
  · exact readsNothing_of_run 20 (by decide) (by decide)
  · exact readsNothing_of_run 20 (by decide) (by decide)

/-- The triage probe after `[ ] x`: reads `x` from `K I` and `y` from `K I'`. -/
theorem triP_x_KI : calculus.Reads ((triP.subst probeX).plug (K ∙ idT)) (V 0) :=
  reads_of_run 20 (by decide) (.var 0)

theorem triP_x_KI' : calculus.Reads ((triP.subst probeX).plug (K ∙ idT')) (V 1) :=
  reads_of_run 20 (by decide) (.var 1)

/-- **In tree calculus the six terms of the bench are pairwise different under probes.**
Listed: the three identities pairwise (triage probe), `K I` against `K I'` (triage after
`[ ] x`), and each pair of SKI's three classes (`[ ] x y`), as in `SKI.six_terms`. -/
theorem tree_six_distinct :
    ¬ calculus.ProbeEq idT idT' ∧ ¬ calculus.ProbeEq idT idT'' ∧ ¬ calculus.ProbeEq idT' idT'' ∧
      ¬ calculus.ProbeEq (K ∙ idT) (K ∙ idT') ∧
      ¬ calculus.ProbeEq idT (K ∙ idT) ∧ ¬ calculus.ProbeEq idT K ∧
      ¬ calculus.ProbeEq (K ∙ idT) K := by
  obtain ⟨-, -, ⟨hI, -, -, hKI, -, hK⟩, ⟨t₁, t₂, t₃, -, -, -⟩⟩ := tree_six_terms
  refine ⟨not_probeEq_of_reads triP t₁ t₂ (by decide), not_probeEq_of_reads triP t₁ t₃ (by decide),
    not_probeEq_of_reads triP t₂ t₃ (by decide),
    not_probeEq_of_reads (triP.subst probeX) triP_x_KI triP_x_KI' (by decide),
    not_probeEq_of_reads probeXY hI hKI (by decide), not_probeEq_of_reads probeXY hI hK (by decide),
    not_probeEq_of_reads probeXY hKI hK (by decide)⟩

/-! ### The rule `S K y → I` is unsound for tree probes -/

/-- The rule `S K y → I`, at the root. -/
def SKRule (t u : Tm ℕ) : Prop := ∃ y, t = L ∙ (L ∙ K) ∙ y ∧ u = idT

/-- **The rule `S K y → I` is unsound in tree calculus.** The identities `S K y` for
`y = △, K, △K` are pairwise different under probes; and any step relation that contains the
rule relates (in one fibre of its conversion) two terms that probes separate, namely `S K K`
and `I`. In SKI the same rule is sound (`SKI.probeEq_SK`). -/
theorem sk_unsound :
    (¬ calculus.ProbeEq idT idT' ∧ ¬ calculus.ProbeEq idT idT'' ∧
      ¬ calculus.ProbeEq idT' idT'') ∧
    ∀ R : Tm ℕ → Tm ℕ → Prop, (∀ t u, SKRule t u → R t u) →
      ∃ t u, EqvGen R t u ∧ ¬ calculus.ProbeEq t u := by
  obtain ⟨h₁, h₂, h₃, -⟩ := tree_six_distinct
  refine ⟨⟨h₁, h₂, h₃⟩, fun R hR => ⟨idT', idT, EqvGen.rel _ _ (hR _ _ ⟨K, rfl, rfl⟩),
    fun h => h₁ fun C r => (h C r).symm⟩⟩

/-! ### Types and the fundamental lemmas -/

/-- `⟦A → B⟧`: applying the term to any member of `A` gives a member of `B`. -/
def Arr (A B : Tm ℕ → Prop) : Tm ℕ → Prop := fun t => ∀ u, A u → B (t ∙ u)

/-- `⟦A → B⟧` is a type as soon as `B` is. -/
theorem isType_arr {A B : Tm ℕ → Prop} (hB : calculus.IsType B) : calculus.IsType (Arr A B) := by
  intro t t' s
  exact forall₂_congr fun u _ => hB (Step.appL u s)

/-- **Fundamental lemma for `K = △△`**: `K ∈ ⟦A → B → A⟧` for every type `A`. -/
theorem fundamental_K {A B : Tm ℕ → Prop} (hA : calculus.IsType A) : Arr A (Arr B A) K :=
  fun u hu v _ => (hA (Step.k u v)).2 hu

/-- **Fundamental lemma for `S x y = △(△x)y`**: if `x ∈ ⟦A → B → C⟧` and `y ∈ ⟦A → B⟧` then
`S x y ∈ ⟦A → C⟧`, for every type `C`. -/
theorem fundamental_S {A B C : Tm ℕ → Prop} (hC : calculus.IsType C) {x y : Tm ℕ}
    (hx : Arr A (Arr B C) x) (hy : Arr A B y) : Arr A C (L ∙ (L ∙ x) ∙ y) :=
  fun z hz => (hC (Step.s x y z)).2 (hx z hz (y ∙ z) (hy z hz))

/-- **Fundamental lemma for triage**: `△(△ w x) y` respects types when its branches do. It
sends a leaf into `C` if `w ∈ C`, a stem `△ u` with `u ∈ A` if `x ∈ ⟦A → C⟧`, and a fork
`△ u v` with `u ∈ A`, `v ∈ B` if `y ∈ ⟦A → B → C⟧`. -/
theorem fundamental_triage {A B C : Tm ℕ → Prop} (hC : calculus.IsType C) {w x y : Tm ℕ}
    (hw : C w) (hx : Arr A C x) (hy : Arr A (Arr B C) y) :
    C (triage w x y ∙ L) ∧ (∀ u, A u → C (triage w x y ∙ (L ∙ u))) ∧
      ∀ u v, A u → B v → C (triage w x y ∙ (L ∙ u ∙ v)) :=
  ⟨(hC (Step.tl w x y)).2 hw, fun u hu => (hC (Step.ts w x y u)).2 (hx u hu),
    fun u v hu hv => (hC (Step.tf w x y u v)).2 (hy u hu v hv)⟩

/-! ### The loop of `ω ω` -/

/-- `ω = S I I = △(△I)I`. -/
def omegaT : Tm ℕ := L ∙ (L ∙ idT) ∙ idT

/-- **`ω ω` runs back to itself**, in five steps: the S-step at the root gives `I ω (I ω)`;
each `I ω` then takes two steps (S, then K) to `ω`, the left one first. (Leftmost-outermost
order does not return: it fires the S-redex of `ω (I ω)` before reducing the argument.) -/
theorem omega_cycle : TransGen Step (omegaT ∙ omegaT) (omegaT ∙ omegaT) :=
  TransGen.head (Step.s idT idT omegaT) <|
    TransGen.head (Step.appL (idT ∙ omegaT) (Step.s K L omegaT)) <|
      TransGen.head (Step.appL (idT ∙ omegaT) (Step.k omegaT (L ∙ omegaT))) <|
        TransGen.head (Step.appR omegaT (Step.s K L omegaT)) <|
          TransGen.single (Step.appR omegaT (Step.k omegaT (L ∙ omegaT)))

end FormalComputation.Tree
