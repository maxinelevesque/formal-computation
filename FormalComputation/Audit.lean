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
