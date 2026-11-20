# Axiom audit

Output of `#print axioms` for every declaration in `FormalComputation/Audit.lean`, from CI
job 2942 on commit `52b5f25` (Lean v4.36.0, Mathlib v4.36.0). The build has no `sorry` in
tiers 1–3. The essay-layer entries are from job 3099 on `9245438`, and the probe-layer
entries from job 3107 on `0fc6620`; neither has any `sorry` outside the stretch files. Every declaration below depends at most on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); none depends on `sorryAx`. CI regenerates
this list on every push (section `==== AXIOMS ====` of the job log).

```
'FormalComputation.le_lOrth_iff_le_rOrth' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.rOrth_of_isIso' depends on axioms: [propext, Classical.choice]
'FormalComputation.rOrth_comp' does not depend on any axioms
'FormalComputation.rOrth_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.rOrth_cancel' does not depend on any axioms
'FormalComputation.rOrth_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.orth_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.orth_iff_restrict_bijective' does not depend on any axioms
'FormalComputation.coerce_restrict' depends on axioms: [Classical.choice, Quot.sound]
'FormalComputation.restrict_coerce' depends on axioms: [Classical.choice, Quot.sound]
'FormalComputation.coerce_id' depends on axioms: [Classical.choice, Quot.sound]
'FormalComputation.coerce_comp' depends on axioms: [Classical.choice, Quot.sound]
'FormalComputation.rOrth_terminal_iff_isLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.steps_le_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.E_le_Conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.beh_iff_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.isRightAdjoint_of_convergent' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.conv_le_of_E_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.conv_iff_isIso_L' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Presentation.unit_mem_Conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.beh_iff_map_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.behEquivInverting' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.behEquivLocalSystems' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.localization_trivial_of_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.beh_equiv_type_of_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.beh_iff_map_bijective_co' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.behEquivLocalSystemsCo' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.beh_equiv_type_of_terminal_co' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.isLocal_of_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.isLocal_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.isLocal_eq_of_le_of_le_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.E_eq_of_le_of_le_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Simulation.adjOnBeh' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Simulation.R_preserves_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Simulation.G_preserves_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Simulation.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.collapse_unfolded' does not depend on any axioms
'FormalComputation.collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.collapse_of_isIso_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.collapse_of_isIso_counit' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.lax_orthogonal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.forget_isEquivalence_of_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.accident' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.not_lax_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Pentagon.wt_top_ne_wt_bot' depends on axioms: [propext, Quot.sound]
'FormalComputation.Pentagon.top_ne_bot_localized' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Pentagon.exists_beh_top_ne_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Pentagon.tamari_beh_bare' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Dehn.dchain_iff_prodConj' depends on axioms: [propext, Quot.sound]
'FormalComputation.Dehn.cost_eq_area' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.kfree_of_step' depends on axioms: [propext]
'FormalComputation.SKI.accident_SKI' does not depend on any axioms
'FormalComputation.SKI.Red.wt_comp' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.omegaLoop_wt' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.kfree_Ω' depends on axioms: [propext]
'FormalComputation.SKI.sq_wt' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.wt_permEq' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.not_absorbed' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.absorbed' depends on axioms: [propext, Quot.sound]

-- essay layer (CI job 3099, commit 9245438)
'FormalComputation.beh_iff_of_subsingleton_co' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.beh_iff_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.IsType.conv' depends on axioms: [Classical.choice]
'FormalComputation.SKI.isType_close' does not depend on any axioms
'FormalComputation.SKI.close_le' depends on axioms: [Classical.choice]
'FormalComputation.SKI.isType_arr' does not depend on any axioms
'FormalComputation.SKI.fundamental_K' does not depend on any axioms
'FormalComputation.SKI.fundamental_I' does not depend on any axioms
'FormalComputation.SKI.fundamental_S' does not depend on any axioms
'FormalComputation.SKI.kaib_one_run' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.omegaLoop_permEq' depends on axioms: [propext, Quot.sound]
'FormalComputation.SKI.not_absorbed'' depends on axioms: [propext, Quot.sound]

-- probe layer (CI job 3107, commit 0fc6620; Lean sources as at 75f2c0d)
'FormalComputation.SKI.confluent' depends on axioms: [Classical.choice]
'FormalComputation.SKI.conv_join' depends on axioms: [Classical.choice]
'FormalComputation.SKI.conv_normal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.three_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probeEq_plug' depends on axioms: [propext]
'FormalComputation.SKI.probeEq_of_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probeEq_SK' depends on axioms: [Classical.choice]
'FormalComputation.SKI.six_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probes_not_running' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.isType_probePred' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.runsToI_not_probe' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.codeEq_iff_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.not_codeEq_I_SKK' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.codeEq_Ia_a' depends on axioms: [propext, Classical.choice, Quot.sound]

-- observation layer (CI job 3115; Lean sources as at mirror commit aefcd90)
'FormalComputation.Obs.Pairing.orth_invariant' depends on axioms: [propext]
'FormalComputation.Obs.Pairing.orth_iUnion' depends on axioms: [propext, Quot.sound]
'FormalComputation.Obs.Lens.preimage_orth' depends on axioms: [propext, Quot.sound]
'FormalComputation.Obs.Lens.same' does not depend on any axioms
'FormalComputation.Obs.familyPairing_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probes_same_iff' does not depend on any axioms
'FormalComputation.SKI.probes_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.isType_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probePred_iff_mem_orth' depends on axioms: [propext]
'FormalComputation.SKI.arr_iff_mem_orth' depends on axioms: [propext, Quot.sound]

-- calculi with probes in general; SKI and tree calculus as instances (CI job 3131; Lean sources as at mirror commit af9324e)
'FormalComputation.Calculus.probeEq_of_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Calculus.probeEq_plug' does not depend on any axioms
'FormalComputation.Calculus.probes_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Calculus.isType_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Calculus.codeEq_iff_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Calculus.conv_normal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.calculus_confluent' depends on axioms: [propext, Classical.choice]
'FormalComputation.SKI.calculus_probeEq_iff' depends on axioms: [propext, Classical.choice]
'FormalComputation.Tree.calculus_confluent' depends on axioms: [propext]
'FormalComputation.Tree.probes_read_code' depends on axioms: [propext, Classical.choice, Quot.sound]

-- tree calculus for the essay, diamond, three classes, V-valued pairings, SKI runs (CI job 3141; branch lean-next 36b67b2, merged into main)
'FormalComputation.Diamond.equal_lengths' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Diamond.length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Diamond.step_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.Lens.preimage_orth_of_toV' depends on axioms: [propext, Quot.sound]
'FormalComputation.Obs.ObsEq.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.ObsEq.same' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.Pairing.toV_orth' depends on axioms: [propext, Quot.sound]
'FormalComputation.Obs.Pairing.toV_same' depends on axioms: [propext]
'FormalComputation.Obs.VLens.preimage_orth' depends on axioms: [propext, Quot.sound]
'FormalComputation.Obs.VLens.same' does not depend on any axioms
'FormalComputation.Obs.VPairing.orth_anti' does not depend on any axioms
'FormalComputation.Obs.VPairing.orth_invariant' depends on axioms: [Quot.sound]
'FormalComputation.Obs.iso_of_obsEq_beh' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_beh_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_beh_of_iso' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_beh_of_iso_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_iff_of_corep' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_of_zigzag' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Obs.obsEq_univ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.conv_iso_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.conv_obsEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.zigzag_of_conv' depends on axioms: [propext]
'FormalComputation.Tree.fundamental_K' depends on axioms: [propext]
'FormalComputation.Tree.fundamental_S' depends on axioms: [propext]
'FormalComputation.Tree.fundamental_triage' depends on axioms: [propext]
'FormalComputation.Tree.omega_cycle' does not depend on any axioms
'FormalComputation.Tree.sk_unsound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Tree.tree_six_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.Tree.tree_six_terms' depends on axioms: [propext, Classical.choice, Quot.sound]

-- linked in the essay, added to the audit in review R1 (CI job 3155)
'FormalComputation.SKI.probePred_respects' does not depend on any axioms
'FormalComputation.SKI.omegaLoop'_wt' depends on axioms: [propext, Quot.sound]

-- linked in the essay after R1 apply (CI job 3164)
'FormalComputation.Obs.Pairing' does not depend on any axioms
'FormalComputation.Presentation' does not depend on any axioms
'FormalComputation.SKI.codeEq_of_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.isType_runsToI' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.le_close' does not depend on any axioms
'FormalComputation.SKI.skRun' does not depend on any axioms

-- closed instances (SKI/Closed.lean; CI jobs 3172 and 3176)
'FormalComputation.SKI.Probe.subst_plug' depends on axioms: [propext]
'FormalComputation.SKI.Step.subst' does not depend on any axioms
'FormalComputation.SKI.conv_subst' depends on axioms: [Classical.choice]
'FormalComputation.SKI.probeEqCl_equivalence' does not depend on any axioms
'FormalComputation.SKI.probeEqCl_iff_of_closed' depends on axioms: [propext]
'FormalComputation.SKI.probeEqCl_of_conv' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.probeEqCl_subst' depends on axioms: [propext]
'FormalComputation.SKI.reds_subst' depends on axioms: [Classical.choice]
'FormalComputation.SKI.not_probeEqCl_aI_aK' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.not_probeEqCl_var_loop' depends on axioms: [propext, Classical.choice]
'FormalComputation.SKI.not_probeEq_II_IK' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalComputation.SKI.not_reads_Ω_app' depends on axioms: [propext, Classical.choice]
'FormalComputation.SKI.probeEqCl_plug' depends on axioms: [propext]
'FormalComputation.SKI.probeEq_aI_aK' depends on axioms: [propext, Classical.choice]
'FormalComputation.SKI.probeEq_not_subst_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
```
