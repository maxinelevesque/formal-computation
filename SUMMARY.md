# Summary: computation as a factorization system

Status labels are explained in `README.md`. Nothing here is machine-checked yet.

## The thesis

Computation is a factorization system on descriptions. Denotation is its
localization. Holes show up as monodromy.

A thing given by a presentation has many descriptions. The descriptions form a
space fibred over the things they describe. Taking connected components
recovers the denotation. Computation is the directed geometry of the fibres,
which taking components forgets. The input-output function that computer
science usually treats as primary is the shadow; the fibre is the object.

## The definition

A **presentation** is a category `P` of descriptions with a class `S` of maps,
the **steps**. In the main example `P` is the category of covariant families
on a category `A` of terms and reductions, and `S` is the generating rewrites.

From `(P, S)` everything else is derived.

- `M` is the class of maps with unique right lifting against `S`. `E` is the
  class with unique left lifting against `M`.
- **Computations** are the maps in `E`.
- **Behaviours** are the objects `X` with `X → 1` in `M`. Equivalently, the
  `S`-local objects.
- **Evaluation** of `X` is the `(E, M)`-factorization `X → LX → 1`. The first
  map is the big step.
- A **trace** is a decomposition of `X → LX` into pushouts of steps. That is
  small-step evaluation.
- **Conversions** are the maps inverted by `L`, the 2-out-of-3 closure of `E`.

The model is the pair `(P, E)`. Keeping only the behaviours loses the
direction.

## What the definition explains

| Rewriting notion | In the framework |
|---|---|
| Normal form | Terminal object of a fibre; a local object |
| Normalization | The unit `X → LX` |
| Confluence | Ore condition; calculus of fractions |
| Knuth–Bendix completion | Adding steps already in `E`, which changes nothing |
| Coherence theorem | Reduction space has contractible components |
| Denotational semantics | Change of base to sets |
| Complexity | Minimal cost of a trace |
| Coercion along a reduction | The unique diagonal filler |

## Main results

1. **Theorem A** [HAND]. In the dynamic picture, behaviours are local systems
   on the reduction groupoid.
2. **Theorem B** [HAND]. A translation or simulation between presentations
   induces an adjunction between behaviour categories. Uniting rule sets
   intersects behaviours. Adding derivable rules changes nothing.
3. **Collapse lemma** [HAND]. Asking for lax orthogonality to a single rule
   forces a unique arrow from each redex to its contractum. So rule cells are
   structure, and direction has to live in the factorization system.
4. **Associativity** [HAND]. With one oriented associativity rule and no
   pentagon, the four-variable reduction space is a circle and evaluation is a
   ℤ-torsor. Imposing the pentagon makes every fibre contractible
   ([MEMORY] Laplaza).
5. **SKI** [HAND]. A model in a one-object groupoid gives a 1-cocycle counting
   S-steps on the right spine. It gives the loop `SII(SII) → SII(SII)` the
   value 1, so that divergence is unavoidable. The loop inside `K a Ω` is
   absorbed by the K-step, so that divergence is avoidable.
6. **Groups** [HAND]. For a group presentation, minimal trace cost equals
   area, so the Dehn function is the complexity function.
7. **Coercion** [HAND]. Coercion along a computation is the unique filler
   against a type family. Its rules for substitution, pairs and equality are
   closure properties of `M`. Functions need a Frobenius condition. The
   universe needs `L` to be left exact.

## Findings worth a second post

- **A trichotomy for loops** [HAND]. The map `End(t) → π₁` separates coherence
  defects, avoidable divergence and unavoidable divergence.
- **Approximation is derived** [HAND]. With a calculus of fractions, the value
  of a term is the ind-object of its reducts. A normal form exists when that
  ind-object is representable.
- **Type theories** [SPEC, partly HAND]. A type theory is a presentation whose
  rules are units and counits of local adjunctions, stable under substitution.
  Polarity predicts which η-laws can be definitional.
- **Dependent type theory has two fibres** [HAND]. Definitional equality is a
  0-truncated orthogonal system. Identity types are a weak one. Known pain
  points sit on the seam.
- **Double category of presentations** [HAND]. Translations are tight and
  simulations loose. A translation has a conjoint exactly when it is
  bisimulation-like.
- **The arena** [CITED]. Invertible coherence calms down in presentable
  ∞-categories, where truncation levels are modes. Direction does not close at
  a finite height, but the tower is regular.

## Open problems

1. The lax theory: factorization systems one directed level up.
2. Higher coherence of the reduction type beyond level 1.
3. Whether identifications are computations sheafified along constructor covers.
4. A dependent type theory with proof-relevant, directed conversion.
5. Whether the loop at Ω survives in full SKI (it does assuming standard
   residual theory).

## Where the detail is

| Note | Contents |
|---|---|
| `notes/01-motif.md` | The structural intuition, the gauge analogy, finiteness |
| `notes/02-knobs.md` | Enrichment, probe shapes, arities, self-classification, the tower |
| `notes/03-definition.md` | The definition, its history, the two pictures, cost, variance |
| `notes/04-examples.md` | SKI, associativity, groups, λ-calculus, naturals, tree calculus |
| `notes/05-morphisms-double-category.md` | Translations, simulations, the double category |
| `notes/06-invariants-directed-gap.md` | Collapse lemma, loops, cocycles, ind-objects |
| `notes/07-type-theory.md` | Adjunction rules, polarity, dependent types, a design |
| `notes/08-coercion.md` | Coercion as a filler, with diagrams |
| `notes/09-arena.md` | Where higher coherence calms down |
| `notes/10-prior-art.md` | References and how each was verified |
| `notes/11-corrections-and-open-problems.md` | What was wrong along the way, and what is open |
