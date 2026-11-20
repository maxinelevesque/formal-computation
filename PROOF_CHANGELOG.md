# Proof changelog

Every change to a statement in `PROOF_MAP.md`, with the node ID, the old statement, the
new one, and why. Additions (new lemmas that make a sentence of the notes precise) are
listed separately from changes. Renames and purely notational fixes are listed last.

Pinned: Lean `v4.36.0`, Mathlib `v4.36.0` (commit `fc4f59e5`).

## Step 2: making the skeleton compile (2026-11-17)

### Statement changes

None of the changes below weakens a statement. Each either makes a pseudo-Lean signature
type-check or fixes something the map left unspecified.

| Node | Old | New | Why |
|---|---|---|---|
| O8 `coe_id`, `coe_comp` | "up to the evident cast" (no statement) | Stated on underlying maps: `(coerce h x d).1 = d.1`; `(coerce (h.comp h') x d).1 = (coerce h' x (coerce h (e' ≫ x) ⟨d.1, _⟩)).1`, with `h : Orth e p`, `h' : Orth e' p` | The fibres `Sec p ((e ≫ e') ≫ x)` and `Sec p (e ≫ (e' ≫ x))` are different types. Comparing underlying maps avoids casts, as the map suggested. `coerce_comp` needs both `e` and `e'` orthogonal to `p`, which the composite statement presupposes. |
| B7 `Translation` | `A`, `A'` arbitrary categories | `A A' : Type v` with `[SmallCategory A]`, `[SmallCategory A']` | What it buys: the pushforward `F_!` is the left Kan extension into `Type v`, which exists when the indexing categories are small. Tier stretch. |
| B7 `adjointTriple_of_hasConjoint` | `: …` (no statement) | `τ.toSimulation.onBeh.IsLeftAdjoint`, assuming `[Reflective 𝒜.toPresentation.Beh.ι]` | Made precise from `notes/05` §5.3: restriction on behaviours has a right adjoint as well as a left one. Tier stretch. |
| C1 `Ins` morphisms | subtype `{u // p.φ ≫ r.map u = l.map u ≫ q.φ}` | structure `Ins.Hom` with fields `u`, `w` (same condition) | Same content; projections on morphisms elaborate reliably. |
| P3 `PartialOrder V4` | order on `V4` itself | order on a copy `Tamari4 := V4` | A `PartialOrder` on `V4` makes `V4` a category (`Preorder.smallCategory`), which would clash with the quiver instance used by `Paths V4`. |
| P3 `pentQuotientEquiv` | relation `fun _ _ f g => (f = top ∧ g = bot)` | inductive `PentRel` with one constructor `PentRel top bot` | The lambda does not type-check for arbitrary endpoints `X Y`. Moved to `Stretch/PentQuotient.lean` (it was marked stretch). |
| K9 | `instance : Category RedCat`, `wtFunctor` (no theorem) | adds `PermEq.comp_congr` and `omegaLoop_infinite_order`: if the image of `loop` under `wtFunctor` is `1`, then `Q.map (loop ^ m) = Q.map (loop ^ n)` implies `m = n` | Makes "the loop has infinite order in the reduction groupoid" a statement. Tier stretch. |

### Additions

| Node | Statement | Why |
|---|---|---|
| O8 | `Orth.id`, `Orth.comp`, `restrict_coerce`, `restrict_id`, `restrict_comp` | Needed to state `coerce_comp`; the map suggested stating functoriality for `restrict`. |
| D4 | `isRightAdjoint_of_convergent [HasTerminal P] [𝒫.Convergent] : 𝒫.Beh.ι.IsRightAdjoint` | The map's suggested first lemma. It is what the size condition buys: every description has a denotation. Stated as `IsRightAdjoint` (a `Prop`) rather than `Reflective` (data). |
| B4 | `E_eq_of_le_of_le_E : 𝒫.steps ≤ 𝒫'.steps → 𝒫'.steps ≤ 𝒫.E → 𝒫'.E = 𝒫.E` | `notes/05` §5.2 and `SUMMARY.md` claim adding rules already in `E` changes neither `E` nor `C`. B4 covers only `C`. |
| C4 | `not_lax_orthogonal : ¬ ∃ adj : Ins.sec Icop (𝟭 Type) ι ⊣ Ins.forget Icop (𝟭 Type), ∀ a, adj.unit.app a = 𝟙 a` | The map's sentence "so this model is not lax orthogonal to the I-rule" follows from C3 and C4; this states it. |
| P2 | `exists_beh_top_ne_bot : ∃ B : PentCat ⥤ Type, pentDyn.toPresentation.Beh B ∧ B.map top ≠ B.map bot` | The map's "with A3: behaviours over this component include sets with a nontrivial automorphism", made precise. |
| P3 | `tamari_beh_bare : Nonempty ((⟨⊤⟩ : DynPresentation Tamari4).toPresentation.Beh.FullSubcategory ≌ Type)` | The map's "then A4 applies". |

### Moves (no change to the statement)

- D6 (`Trace`, `length`, `mem_E`) → `Stretch/Trace.lean`; B7 → `Stretch/Conjoint.lean`;
  the stretch part of P3 → `Stretch/PentQuotient.lean`; K9 → `Stretch/RedCat.lean`. Tier
  stretch is kept out of the tier modules so a tier can be sorry-free on its own.
- K7 `not_absorbed` → `SKI/PermEq.lean`, because it uses K6.

### Renames and notation

- O8 `coe` → `coerce`, `coe_restrict` → `coerce_restrict` (avoids confusion with Lean's
  coercion machinery).
- C4: morphisms in `Type` are now a wrapper structure in Mathlib (`TypeCat.Hom`), so
  functions are promoted with `↾`: `map f := ↾(Prod.map f id)`, `app _ := ↾Prod.fst`.
  `whiskerLeft`/`whiskerRight` are `Functor.whiskerLeft`/`Functor.whiskerRight`.
- P1: `V4` derives `DecidableEq` only (`deriving Fintype` failed to elaborate and is not needed).
- P1: `Paths.of.obj V4.a` → `pv .a` (`Paths.of` takes the quiver explicitly); edges as
  morphisms are `ed .ab` etc.
- K5: `⟦a, b⟧` is written `r2 a b` (also `r1`, `r3`); `EqvGen` → `Relation.EqvGen`;
  `p.mapAppL u` → `Red.mapAppL u p`. The infix `⬝` is scoped to `FormalComputation.SKI`.
- Presentations are named `𝔓` (Fraktur), not `𝒫`: in Mathlib `𝒫` is the powerset
  notation, so it cannot be a variable name.
- Universe levels are explicit throughout. A4 states the point as `Discrete PUnit.{w + 1}`
  for every `w`.

## Tier 1 (2026-11-17)

### Statement changes

The variance change was decided with Maxine before any tier-1 proof was written. None of
these weakens a statement: each old statement is still proved, under a new name.

| Node | Old | New | Why |
|---|---|---|---|
| D5 `toPresentation` | `Presentation (A ⥤ Type v)`, steps the arrows isomorphic to `coyoneda.map s.op` | `Presentation (Aᵒᵖ ⥤ Type v)`, steps `𝒜.steps.map yoneda` (Mathlib's `MorphismProperty.map`: arrows isomorphic to `yoneda.map s`) | `notes/03` §3.4 says descriptions are presheaves. Under covariant families a step map runs `Hom(t′, –) → Hom(t, –)`, contractum to redex, so `E` and traces point backwards. The old presentation is kept as `toCopresentation` (`𝒜.steps.op.map coyoneda`, the map's definition up to the direction of the arrow isomorphism). |
| A1 `beh_iff_map_bijective` | `B : A ⥤ Type v`, `Bijective (B.map s)` | `B : Aᵒᵖ ⥤ Type v`, `Bijective (B.map s.op)` | Follows D5. An observation acts on a step contravariantly (Yoneda). Old statement: `beh_iff_map_bijective_co`. |
| A2 `behEquivInverting` | `≌ 𝒜.steps.FunctorsInverting (Type v)` | `≌ 𝒜.steps.op.FunctorsInverting (Type v)` | Follows D5. Old: `behEquivInvertingCo`. |
| A3 `behEquivLocalSystems` | `≌ (𝒜.steps.Localization ⥤ Type v)` | `≌ (𝒜.steps.op.Localization ⥤ Type v)`, the localization of `Aᵒᵖ` | Follows D5. Old: `behEquivLocalSystemsCo`. Identifying this localization with `(A[S⁻¹])ᵒᵖ`, and with `A[S⁻¹]` when that is a groupoid, is not formalized. |
| A4 `beh_equiv_type_of_terminal` | about `A ⥤ Type v` | same statement about presheaves | Uses the initial object `op n` of `Aᵒᵖ`. Old: `beh_equiv_type_of_terminal_co`. `localization_trivial_of_terminal` is unchanged. |
| P2 `exists_beh_top_ne_bot` | `B : PentCat ⥤ Type`, `B.map top ≠ B.map bot` | `B : PentCatᵒᵖ ⥤ Type`, `B.map top.op ≠ B.map bot.op` | Follows D5 (tier 2; not yet proved). |
| B7 `Translation`, `HasConjoint` | `coyoneda.map (F.map s).op`; restriction along `F` on `A' ⥤ Type v` | `yoneda.map (F.map s)`; restriction along `F.op` on `A'ᵒᵖ ⥤ Type v` | Follows D5 (tier stretch). |

### Additions

| Node | Statement | Why |
|---|---|---|
| O4 | `Orth.comp_right` | Composition in the right variable; gives `rOrth_comp`. |
| O9 | `orth_terminal_iff : Orth f (terminal.from X) ↔ Bijective (f ≫ ·)` | Shared by O9 and D3. |
| O | `lOrth_of_isIso` | Isomorphisms are computations; used by `conv_le_of_E_le`. |
| D3 | `beh_of_M`, `conv_iff_range` | `conv_iff_range` restates `Conv` in the form Mathlib's Bousfield lemmas use (`ObjectProperty.isLocal (· ∈ Set.range ι.obj)`). |
| D4 | `conv_le_of_E_le [HasTerminal P] [Convergent] (W) [W.HasTwoOutOfThreeProperty] : 𝔓.E ≤ W → 𝔓.Conv ≤ W` | Makes "conversions are the 2-out-of-3 closure of `E`" precise. It needs convergence; `notes/03` and `SUMMARY.md` now say so. |
| D4 | `attribute [instance] Convergent.fac` | Lets Mathlib's `factorizationData` find the factorization. |
| A | `bijective_precomp_iff`, `isLocal_map_iff`, `beh_eq_isInvertedBy` | Locality is invariant under isomorphism of arrows, so the steps of D5 can be taken up to isomorphism. |
| A4 | `starAdjOfTerminal`, `fromPUnitAdjOfInitial`, `localization_trivial_of_terminal'`, `localization_trivial_of_initial'` | A4 for any class equal to `⊤`, via Mathlib's `Adjunction.isLocalization`: the functor to the point is a localization because it has a fully faithful adjoint. |
| A1–A4 | `beh_iff_map_bijective_co`, `behEquivInvertingCo`, `behEquivLocalSystemsCo`, `beh_equiv_type_of_terminal_co` | Theorem A for the covariant presentation. |
| C3′ | `secAdjOfUnique`, `lax_orthogonal_iff : (∃ adj : sec ρ ⊣ forget, ∀ a, adj.unit.app a = 𝟙 a) ↔ ∀ a φ, φ = ρ.app a`, `forget_isEquivalence_of_unique` | The collapse lemma is a characterization: lax orthogonality to a free rule is exactly uniqueness of arrows `l a ⟶ r a`, and then `forget` is an equivalence. |
| C3″ | `collapse_of_isIso_unit`, `collapse_of_isIso_counit` | The collapse does not depend on the convention: an invertible unit, or a right adjoint section with invertible counit, collapses the same way. `collapse` is now derived from `collapse_of_isIso_unit`. |
| C4 | `accident_app` | The accident at `a = Unit`; `accident` and `not_lax_orthogonal` use it. |

### Notes changed

- `notes/03` §3.2 item 9 and `SUMMARY.md`: conversions are the 2-out-of-3 closure of `E`
  *when the presentation is convergent*.
- `notes/03` §3.4: the two variances agree on behaviours when the steps generate `A`;
  Theorem A is formalized in both.
- `notes/03` §3.6: convergence implies the reflector exists; the claimed equivalence is
  only one direction.
- `notes/11` §11.1: rows 15–18 record these.

## Tiers 2 and 3 (2026-11-17)

No statement changes. Additions and notation:

| Node | Change | Why |
|---|---|---|
| P2 | adds `wtB : PentCatᵒᵖ ⥤ Type` (every bracketing ↦ `ℤ`, a reduction adds its weight) | The behaviour that witnesses `exists_beh_top_ne_bot`. |
| G3 | adds `isProdConj_of_dchain` (a chain `g ⇝ k` writes `g k⁻¹` as a product of conjugates) and `dchain_of_isProdConj` | The two directions of `dchain_iff_prodConj`. |
| K2 | adds `kfree_of_red` | Reduction keeps the K-free fragment; used by K6 for whiskered squares. |
| K4 | adds `Red.wt_mapAppL` (weight 0), `Red.wt_mapAppR` (weight kept) | Weights of reductions in context. |
| K6 | adds `sq_wt` (each generating square preserves the weight on a K-free source) | K6 is the equivalence closure of this. The two K-naturality squares are the ones that need K-freeness: `k_nat₂` erases an argument step, which can carry weight. |
| K7 | `sii`, `Ω` are `abbrev` rather than `def` | So that the endpoints of `omegaLoop` match the equation lemmas of `Red.wt` at reducible transparency. Same terms. |

## Essay layer (2026-11-19)

From the essay `post/atoms-and-probes.html`. Additions only; no statement changed.
Green at `9245438` (CI job 3099), axioms in `AXIOMS.md`.

- `FormalComputation/SKI/Types.lean`: `IsType` (a predicate that leaks along no step),
  `Conv`, `IsType.conv`, `isType_of_conv`, `close`, `le_close`, `isType_close`, `close_le`,
  `Arr`, `isType_arr`, `fundamental_K`, `fundamental_I`, `fundamental_S`, `skRun`,
  `kaib_one_run`, `omegaLoop'` (the loop in the essay's order), `omegaLoop'_wt`,
  `omegaLoop_permEq`, `not_absorbed'`.
- `FormalComputation/Predicates.lean`: `beh_iff_of_subsingleton_co` and
  `beh_iff_of_subsingleton`. A subsingleton-valued family is a behaviour iff it does not
  leak. This connects the essay's definition of a type to Theorem A.
- Observation: the fundamental lemmas use only the backward half of non-leaking (subject
  expansion), and `fundamental_S` needs only its result predicate to be a type.

## Probe layer (2026-11-19)

Green at `75f2c0d` (CI job 3106).

- **K1 changed (statement): `Tm` gains variables** (`Tm.var : ℕ → Tm`), and `KFree` is
  extended (`var` is K-free). Reason: the essay's probes supply variables and read them
  back. No other statement changed; every earlier proof goes through unchanged.
- `FormalComputation/SKI/Confluence.lean` (additions): `Par`, `par_diamond`, `confluent`,
  `conv_join`, `IsNormal`, `reds_normal`, `conv_normal_eq`, `reds_of_conv_normal`,
  `three_fibres`.
- `FormalComputation/SKI/Probes.lean` (additions): `InVars`, `Probe` (multi-hole contexts),
  `Reads`, `ProbeEq`, `probeEq_plug`, `reads_unique`, `probeEq_of_conv`, `Sim`,
  `probeEq_of_sim`, `probeEq_SK`, `six_terms`, `probes_not_running`, `ProbePred`,
  `isType_probePred`, `probePred_respects`, `isType_runsToI`, `runsToI_not_probe`,
  `ReadsCode`, `CodeEq`, `codeEq_of_conv`, `codeEq_iff_conv`, `not_codeEq_I_SKK`,
  `codeEq_Ia_a`.
- Design choice, logged: probes are contexts with any number of holes, and a probe reads an
  outcome when the run reaches a term written in variables alone. This matches the essay's
  figure (its reducer reads any outcome free of `S`, `K`, `I`). With multi-hole contexts,
  "same under every probe" is at least as strong as with single-hole contexts.

## Observation layer (2026-11-19)

Additions only; no earlier statement changed. Green at CI job 3115 (mirror commit aefcd90).

- **Design decision (Maxine):** observation is a pairing between descriptions and observers
  (`Obs.Pairing`), with families of the framework as a special case (`Obs.familyPairing`).
  Truth-valued for now. See `notes/12-observation.md` §12.6.
- `Observation.lean`: `T^⊥` (`orth`), sameness, invariance; every `T^⊥` of an invariant
  pairing is a type; lenses (Chu morphisms) compose, carry sameness forward, and pull
  `T^⊥` back to `(put T)^⊥`; behaviour predicates give an invariant pairing.
- `SKI/Lenses.lean`: the essay's probes as a pairing (`probes_same_iff`: its sameness is
  `ProbeEq`), invariant by confluence; `isType_orth`; `probePred_iff_mem_orth`; the lens
  "apply to `a`"; arrow types built from lenses (`arr_iff_mem_orth`). §12.7.

## Calculi with probes; tree calculus (2026-11-19)

Additions only; no earlier statement changed. Green at CI job 3131.

- `Calculus.lean`: the essay's probe results for any calculus with multi-hole contexts,
  outcomes that do not step, and confluence: the chain text ⇒ running ⇒ probes,
  congruence (as a lens), the invariant probe pairing and its types, and code-reading
  probes seeing exactly what running sees on terms with a value.
- `SKI/Instance.lean`: SKI is an instance; the general notions agree with the SKI ones
  (sameness under probes and after running by definition; code equality via normal forms).
- `Tree/Calculus.lean`: tree calculus (triage presentation) with variables. Parallel
  reduction, complete development and the diamond are ported from `tree-semantics`
  (`TreeCalculus/Algebra.lean`), unchanged up to namespace. New: one-step reduction,
  confluence, probes, the instance, a certified evaluator, and `probes_read_code`
  (`S K △` and `S K K` agree on every argument, lie in different fibres, and a triage
  probe separates them).
- Design choice: tree-calculus terms carry variables, as SKI's do (K1), so that probes
  read outcomes written in variables. This matches the essay's probes and is not the
  closed-tree setting of `tree-semantics`.

## Tree calculus for the essay; diamond; three classes; V-valued pairings (2026-11-19)

Additions only. Green at CI job 3141 (branch `lean-next`, merged).

- `Tree/Essay.lean`:
  - `tree_six_terms`: 24 cells, the six tree terms under the three probes and the triage
    probe `triP`; the first three rows match SKI's `six_terms`.
  - `tree_six_distinct`.
  - `sk_unsound`: the rule `S K y → I` identifies terms that probes separate.
  - `isType_arr`, `fundamental_K`, `fundamental_S`, `fundamental_triage`.
  - `omega_cycle`. The cycle reduces the argument first; leftmost-outermost order does
    not return to `ω ω`.
- `Diamond.lean`: under the one-step diamond (interaction nets),
  - `equal_lengths`: runs to normal form have equal length and the same end;
  - `step_cost`;
  - `length_le`, so a term with a normal form has no infinite run.
- `ThreeClasses.lean`: `ObsEq 𝒪` is sameness under a class of covariant families.
  - Natural bijections of the evaluations are required.
  - `obsEq_univ_iff`: all families ↔ isomorphic in `A`.
  - `obsEq_beh_iff`: behaviours ↔ isomorphic in the localization.
    - **Stated hypothesis:** the localization's hom-sets lie in `Type v`. This is needed so
      that its corepresentables are behaviours.
    - The direction from isomorphic to `ObsEq` holds without the hypothesis, for any
      localization (`obsEq_beh_of_iso`).
  - `obsEq_of_zigzag`: invariant observers do not separate a zigzag of steps.
- `Observation.lean`: V-valued pairings and lenses (`VPairing`, `VLens`).
  - `orth_invariant`, `orth_anti`, `preimage_orth`, `same`.
  - With V = Prop they agree with `Pairing` (`toV_orth`, `toV_same`,
    `preimage_orth_of_toV`).
- `SKI/Dyn.lean`: SKI runs as a `DynPresentation` on `Paths Tm`.
  - `conv_obsEq`, `conv_iso_Q`: conversion gives sameness under behaviours, and an
    isomorphism in the localization.
  - The converses are not proved.

## Closed instances: the essay's reading rule (2026-11-20)

**Decision (Maxine, on the lead's recommendation).** The essay reads outcomes only on terms
without variables. Terms with variables are compared through all their closed instances
(`ProbeEqCl`), the largest substitution-stable equality inside sameness under probes.

The two simpler rules fail:
- **The permissive rule (`ProbeEq`, as in the earlier Lean).** It reads the term's own
  variables. It is not stable under substitution: `probeEq_not_subst_stable` (`a I` ≡ `a K`,
  yet `I I` ≢ `I K`).
- **The strict rule (only the probe's fresh variables are readable, on open terms).** It makes
  a variable look like a term with no value. This is argued, not mechanized.

On terms without variables the three agree (`probeEqCl_iff_of_closed`). So every earlier
result about closed terms is unchanged, and no statement was weakened.

`SKI/Closed.lean` adds:
- substitution, and steps, runs and conversion stable under it;
- `ProbeEqCl` with `probeEqCl_of_conv`, `probeEqCl_subst` (for any substitution) and
  `probeEqCl_plug`;
- `not_probeEqCl_var_loop`;
- `not_probeEqCl_aI_aK`;
- `probeEq_aI_aK`, by a swap simulation.

Green at CI job 3172.

## Mathlib anchors (checked against v4.36.0 source)

| Anchor | Status |
|---|---|
| `MorphismProperty`, `≤`, `⊔`, `⊤` | present (`MorphismProperty/Basic.lean`, a `CompleteBooleanAlgebra`) |
| `MorphismProperty.isLocal : ObjectProperty C` | present (`ObjectProperty/Local.lean`); also `isLocal_iSup` |
| `ObjectProperty.isLocal : MorphismProperty C` | present (`Localization/Bousfield.lean`), with `HasTwoOutOfThreeProperty` instance and `isLocal_iff_isIso_map` for a reflective subcategory |
| `ObjectProperty.FullSubcategory`, `ObjectProperty.ι` | present (`ObjectProperty/FullSubcategory.lean`) |
| `Reflective`, `reflector`, `reflectorAdjunction` | present (`Adjunction/Reflective.lean`); `Reflective` is a class on the inclusion functor |
| `MorphismProperty.HasFactorization` | present (`MorphismProperty/Factorization.lean`), arguments `W₁ W₂` |
| `MorphismProperty.HasTwoOutOfThreeProperty` | present (`MorphismProperty/Composition.lean`) |
| `MorphismProperty.Localization`, `.Q`, `.FunctorsInverting` | present (`Localization/Construction.lean`, `MorphismProperty/IsInvertedBy.lean`) |
| `Localization.functorEquivalence`, `whiskeringLeftFunctor'` | present (`Localization/Predicate.lean`) |
| `MorphismProperty.HasLeftCalculusOfFractions` | present (`Localization/CalculusOfFractions.lean`); not used (N3 is not formalized) |
| `CategoryTheory.OrthogonalReflection` | present (`Presentable/OrthogonalReflection.lean`); not used |
| `HasLiftingProperty`, `MorphismProperty.llp`, `rlp` | present (`LiftingProperties/Basic.lean`, `MorphismProperty/LiftingProperty.lean`); existence-only, not used |
| `Adjunction.hasLiftingProperty_iff` | present (`LiftingProperties/Adjunction.lean`); existence-only analogue of O6 |
| `IsPullback`, `IsPushout` | present (`Limits/Shapes/Pullback/IsPullback/Defs.lean`) |
| `pullback.diagonal` | present (`Limits/Shapes/Diagonal.lean`) |
| `coyoneda`, `Arrow` | present |
| `Paths`, `Quiver.Path`, `CategoryTheory.Quotient` | present; `Paths.of V` takes `V` explicitly; `Paths.lift` for functors out |
| `SingleObj`, `Multiplicative` | present (`SingleObj` abbreviates `Quiver.SingleObj`; it is a groupoid for a group) |
| `FreeGroup` | present |
| `EqvGen` | renamed: `Relation.EqvGen` (`Logic/Relation.lean`) |
| `End X` | changed: a structure (`End.of`, `.asHom`), no longer a synonym for `X ⟶ X` |
| Morphisms in `Type` | changed since the map was written: a wrapper `TypeCat.Hom`, coerced to functions; `↾f` promotes a function |
