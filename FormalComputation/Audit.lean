import FormalComputation

/-!
# Axiom audit

Not imported by the library. CI elaborates this file after the build and prints the axioms
each verified declaration depends on. Anything the post calls verified must depend only on
`propext`, `Classical.choice` and `Quot.sound`, and never on `sorryAx`.
-/

open FormalComputation

-- Tier 1: orthogonality and coercion (O1–O9)
#print axioms le_lOrth_iff_le_rOrth
#print axioms rOrth_of_isIso
#print axioms rOrth_comp
#print axioms rOrth_of_isPullback
#print axioms rOrth_cancel
#print axioms rOrth_diagonal
#print axioms orth_adj
#print axioms orth_iff_restrict_bijective
#print axioms coerce_restrict
#print axioms restrict_coerce
#print axioms coerce_id
#print axioms coerce_comp
#print axioms rOrth_terminal_iff_isLocal

-- Tier 1: presentations (D3, D4)
#print axioms Presentation.steps_le_E
#print axioms Presentation.E_le_Conv
#print axioms Presentation.beh_iff_M
#print axioms Presentation.isRightAdjoint_of_convergent
#print axioms Presentation.conv_le_of_E_le
#print axioms Presentation.conv_iff_isIso_L
#print axioms Presentation.unit_mem_Conv

-- Tier 1: Theorem A (A1–A4), both variances
#print axioms beh_iff_map_bijective
#print axioms behEquivInverting
#print axioms behEquivLocalSystems
#print axioms localization_trivial_of_terminal
#print axioms beh_equiv_type_of_terminal
#print axioms beh_iff_map_bijective_co
#print axioms behEquivLocalSystemsCo
#print axioms beh_equiv_type_of_terminal_co

-- Tier 1: Theorem B (B1–B6)
#print axioms isLocal_of_adj
#print axioms isLocal_sup
#print axioms isLocal_eq_of_le_of_le_conv
#print axioms E_eq_of_le_of_le_E
#print axioms Simulation.adjOnBeh
#print axioms Simulation.R_preserves_M
#print axioms Simulation.G_preserves_E
#print axioms Simulation.comp

-- Tier 1: the collapse lemma (C2–C4)
#print axioms collapse_unfolded
#print axioms collapse
#print axioms collapse_of_isIso_unit
#print axioms collapse_of_isIso_counit
#print axioms lax_orthogonal_iff
#print axioms forget_isEquivalence_of_unique
#print axioms accident
#print axioms not_lax_orthogonal

-- Tier 2: the pentagon (P1–P3)
#print axioms Pentagon.wt_top_ne_wt_bot
#print axioms Pentagon.top_ne_bot_localized
#print axioms Pentagon.exists_beh_top_ne_bot
#print axioms Pentagon.tamari_beh_bare

-- Tier 2: cost equals area (G1–G3)
#print axioms Dehn.dchain_iff_prodConj
#print axioms Dehn.cost_eq_area

-- Tier 3: SKI (K1–K8)
#print axioms SKI.kfree_of_step
#print axioms SKI.accident_SKI
#print axioms SKI.Red.wt_comp
#print axioms SKI.omegaLoop_wt
#print axioms SKI.kfree_Ω
#print axioms SKI.sq_wt
#print axioms SKI.wt_permEq
#print axioms SKI.not_absorbed
#print axioms SKI.absorbed

-- The essay layer ("Atoms and Probes")
#print axioms beh_iff_of_subsingleton_co
#print axioms beh_iff_of_subsingleton
#print axioms SKI.IsType.conv
#print axioms SKI.isType_close
#print axioms SKI.close_le
#print axioms SKI.isType_arr
#print axioms SKI.fundamental_K
#print axioms SKI.fundamental_I
#print axioms SKI.fundamental_S
#print axioms SKI.kaib_one_run
#print axioms SKI.omegaLoop_permEq
#print axioms SKI.not_absorbed'
#print axioms SKI.confluent
#print axioms SKI.conv_join
#print axioms SKI.conv_normal_eq
#print axioms SKI.three_fibres
#print axioms SKI.probeEq_plug
#print axioms SKI.probeEq_of_conv
#print axioms SKI.probeEq_SK
#print axioms SKI.six_terms
#print axioms SKI.probes_not_running
#print axioms SKI.isType_probePred
#print axioms SKI.runsToI_not_probe
#print axioms SKI.codeEq_iff_conv
#print axioms SKI.not_codeEq_I_SKK
#print axioms SKI.codeEq_Ia_a
-- Probes read closed terms
#print axioms SKI.probeEqCl_plug
#print axioms SKI.not_reads_Ω_app
#print axioms SKI.not_probeEqCl_var_loop
#print axioms SKI.not_probeEq_II_IK
#print axioms SKI.not_probeEqCl_aI_aK
#print axioms SKI.probeEq_aI_aK
#print axioms SKI.probeEq_not_subst_stable
-- Observation as a pairing, and lenses
#print axioms Obs.Pairing.orth_invariant
#print axioms Obs.Pairing.orth_iUnion
#print axioms Obs.Lens.preimage_orth
#print axioms Obs.Lens.same
#print axioms Obs.familyPairing_invariant
#print axioms SKI.probes_same_iff
#print axioms SKI.probes_invariant
#print axioms SKI.isType_orth
#print axioms SKI.probePred_iff_mem_orth
#print axioms SKI.arr_iff_mem_orth
-- Calculi with probes, in general; SKI as an instance
#print axioms Calculus.probeEq_of_conv
#print axioms Calculus.probeEq_plug
#print axioms Calculus.probes_invariant
#print axioms Calculus.isType_orth
#print axioms Calculus.codeEq_iff_conv
#print axioms Calculus.conv_normal_eq
#print axioms SKI.calculus_confluent
#print axioms SKI.calculus_probeEq_iff
-- Tree calculus as a calculus with probes
#print axioms Tree.calculus_confluent
#print axioms Tree.probes_read_code
-- Tree calculus in the essay's figures (the calculus switch)
#print axioms Tree.tree_six_terms
#print axioms Tree.tree_six_distinct
#print axioms Tree.sk_unsound
#print axioms Tree.isType_arr
#print axioms Tree.fundamental_K
#print axioms Tree.fundamental_S
#print axioms Tree.fundamental_triage
#print axioms Tree.omega_cycle
-- A one-step diamond makes cost a property of the term
#print axioms Diamond.equal_lengths
#print axioms Diamond.step_cost
#print axioms Diamond.length_le
-- Three classes of observers
#print axioms Obs.ObsEq.mono
#print axioms Obs.ObsEq.same
#print axioms Obs.obsEq_univ_iff
#print axioms Obs.obsEq_iff_of_corep
#print axioms Obs.iso_of_obsEq_beh
#print axioms Obs.obsEq_beh_of_iso
#print axioms Obs.obsEq_beh_iff
#print axioms Obs.obsEq_beh_of_iso_Q
#print axioms Obs.obsEq_of_zigzag
-- Pairings valued in a complete lattice
#print axioms Obs.VPairing.orth_invariant
#print axioms Obs.VPairing.orth_anti
#print axioms Obs.VLens.preimage_orth
#print axioms Obs.VLens.same
#print axioms Obs.Pairing.toV_orth
#print axioms Obs.Pairing.toV_same
#print axioms Obs.Lens.preimage_orth_of_toV
-- SKI runs as a dynamic presentation
#print axioms SKI.zigzag_of_conv
#print axioms SKI.conv_obsEq
#print axioms SKI.conv_iso_Q
-- linked in the essay but missing from the audit (R1, L pass)
#print axioms SKI.probePred_respects
#print axioms SKI.omegaLoop'_wt
-- linked in the essay after R1 apply
#print axioms SKI.skRun
#print axioms SKI.le_close
#print axioms SKI.isType_runsToI
#print axioms SKI.codeEq_of_conv
#print axioms Obs.Pairing
#print axioms Presentation
-- closed instances (moved to the end so the CI log tail shows them)
#print axioms SKI.Step.subst
#print axioms SKI.reds_subst
#print axioms SKI.conv_subst
#print axioms SKI.Probe.subst_plug
#print axioms SKI.probeEqCl_equivalence
#print axioms SKI.probeEqCl_of_conv
#print axioms SKI.probeEqCl_iff_of_closed
#print axioms SKI.probeEqCl_subst
