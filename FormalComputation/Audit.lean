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
