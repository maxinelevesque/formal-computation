# Axiom audit

Output of `#print axioms` for every declaration in `FormalComputation/Audit.lean`, from CI
job 2942 on commit `c40763e` (Lean v4.36.0, Mathlib v4.36.0). The build has no `sorry` in
tiers 1–3. The essay-layer entries at the end are from job 3099 on `95590cb`, which has
no `sorry` outside the stretch files. Every declaration below depends at most on Lean's three standard axioms
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

-- essay layer (CI job 3099, commit 95590cb)
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
```
