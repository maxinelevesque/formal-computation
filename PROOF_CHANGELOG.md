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
- P1: `Paths.of.obj V4.a` → `pv .a` (`Paths.of` takes the quiver explicitly); edges as
  morphisms are `ed .ab` etc.
- K5: `⟦a, b⟧` is written `r2 a b` (also `r1`, `r3`); `EqvGen` → `Relation.EqvGen`;
  `p.mapAppL u` → `Red.mapAppL u p`. The infix `⬝` is scoped to `FormalComputation.SKI`.
- Presentations are named `𝔓` (Fraktur), not `𝒫`: in Mathlib `𝒫` is the powerset
  notation, so it cannot be a variable name.
- Universe levels are explicit throughout. A4 states the point as `Discrete PUnit.{w + 1}`
  for every `w`.

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
| Morphisms in `Type` | changed since the map was written: a wrapper `TypeCat.Hom`, coerced to functions; `↾f` promotes a function |
