# 3. The definition

## 3.1 How it got here

**Version 0.** A model was a tuple `(V, A, Φ, S)`: a cosmos, a category of
probes, a class of weights, and a class `S` of maps in `Φ(A)`. Behaviours `C`
were the presheaves orthogonal to `S`, and the internal bundle was the
reflection `L : Φ(A) → C`.

This already matched many anchors (§3.7). Three gaps were recorded.

- Orthogonality inverts steps, so direction survived only in `S`.
- Realizability entered through `Φ` and not through `S`.
- Existence of `L` needs hypotheses.

**The failed repair.** To keep direction, encode a rule `l ⇒ r` as "freely
add a 2-cell" and ask for lax orthogonality (universal fillers, as in
Clementino and López Franco). This fails: it forces a unique arrow from each
redex to its contractum (the collapse lemma, `06` §6.1). Rule cells are
structure, not property.

**Version 1.** Direction belongs to a factorization system, not to individual
rules. That is the definition below.

## 3.2 Definition (version 1)

A **presentation** is a triple `(V, A, S)`.

1. `V` is a cosmos, the object of observations.
2. `A` is a `V`-category of probes. Write `P` for the `V`-category of families
   on `A` (see §3.4 for variance).
3. `S` is a set of maps in `P`, the **steps**.

Derived:

4. `M` is the class of maps right orthogonal to `S` (unique lifting). `E` is
   the class left orthogonal to `M`. When `(E, M)` is a factorization system,
   the presentation is **convergent**.
5. **Computations** are the maps in `E`.
6. **Behaviours** are the `X` with `X → 1` in `M`. They form `C`. These are
   exactly the `S`-local objects.
7. **Evaluation** is the factorization `X → LX → 1`. The first map is the big
   step.
8. A **trace** is a decomposition of `X → LX` into pushouts of steps (and
   composites of such). That is small-step evaluation.
9. **Conversions** are the maps `L` inverts. When the presentation is
   convergent, they are the 2-out-of-3 closure of `E` [LEAN:
   `Presentation.conv_le_of_E_le`]. Without convergence, `E ≤ Conv` and
   `Conv` has 2-out-of-3, but nothing shown here makes it the least such
   class.

**The model is the pair `(P, E)`, not the quotient `C`.**

For the Lean work the definition is stated in an arbitrary category `P` with a
`MorphismProperty` of steps; `V = Set` throughout. See `PROOF_MAP.md` D1–D6.

**On direction.** [CITED] A factorization system corresponds to a reflective
localization exactly when its left class satisfies 2-out-of-3 (Cassidy, Hébert
and Kelly). Closing `E` under 2-out-of-3 turns reductions into conversions.
Caution: on representables in the dynamic picture, every map of `A` is already
a composite of steps, so the gap between `E` and its closure is visible only
on non-representable objects. The primary carrier of direction is that the
steps are maps which are not isomorphisms in `P` but become so in `C`.

## 3.3 Two pictures

There are two natural choices of probe. The first definition hid this.

**Algebraic picture.** Probes are contexts (free algebras `F(n)`); terms are
elements; a rule is a parallel pair `l, r : F(1) ⇉ F(n)`; a step is the
quotient map forcing `l = r`. `C` is the models of the theory. Rule
orientation is invisible unless `V` is at least Pos.

Level by level in the algebraic picture, for a rule `l ⇒ r`:

- `V = Set`: a step forces `l = r`. A fibre is a bare set of convertible terms.
- `V = Pos`: a step forces `l ≥ r`. Fibres are reduction preorders. Confluence
  is a property.
- `V = Cat`: a step freely adds a 2-cell. Fibres are categories of reduction
  sequences modulo interchange. Confluence becomes structure, so one can ask
  whether the squares commute.
- `V` = spaces or ω-categories: cells between cells are kept. Holes can live
  here.

**Dynamic picture.** Probes are terms. `A` is the category of terms and
reductions (modulo whatever equations between reductions have been imposed).
Steps are the rule instances `t → u`. Then:

> **Theorem A** [HAND]. `C` is the category of local systems on the reduction
> groupoid: families on `A` that invert every step, equivalently functors out
> of the localization of `A` at the steps.

With `V` = spaces, `C` is spaces over the classifying space of `A`.

**Relation between the pictures.** The dynamic picture over spaces is the
algebraic picture over Cat with each hom-category replaced by its classifying
space. So the change-of-base ladder is

    Cat  →  spaces  →  Set

with Squier-type invariants on the middle rung. This adds a rung to the
Baez–Williams ladder.

**What coherence means.** A coherence theorem says the reduction space has
contractible components. Equivalently behaviours are a bare set of values and
evaluation is path-independent. If a fibre has a terminal object, its
component is contractible (PROOF_MAP A4).

## 3.4 Variance

Two variances are in play, and both are needed.

- **Descriptions are representable presheaves.** A term `t` is `y(t) = A(–, t)`
  in `Aᵒᵖ ⥤ Type`. This is covariant in `t`, so a reduction `t → t′` gives
  `y(t) → y(t′)`. Evaluation of a term is `L y(t)` (`06` §6.5).
- **Type families over terms are covariant functors** `B : A ⥤ Type`: a
  reduction `t → t′` pushes the fibre at `t` forward to the fibre at `t′`. A
  step `s : t → t′` appears among such families as the map
  `Hom(t′, –) → Hom(t, –)`, and `B` is local for it exactly when `B(s)` is a
  bijection.

For local objects the two agree when the steps generate `A` (every
reduction is a composite of steps): then the localization at the steps is a
groupoid, isomorphic to its opposite [HAND]. Theorem A is formalized in both
variances; the main statement is for presheaves, where computations run
forward and an observation `Z` acts on a step `s : t → t′` contravariantly,
by `Z(s) : Z(t′) → Z(t)` (Yoneda). Behaviours are the observers that cannot
see the direction of a step. Under covariant families the step map runs
`Hom(t′, –) → Hom(t, –)`, so `E` points from contractum to redex there; that
presentation is the one for type families and coercion. See
`PROOF_CHANGELOG.md` (tier 1).

The difference matters for exactness of `L` (`08` §8.6). For covariant
families, `(LB)(t)` is a colimit over reducts of `t`, which confluence makes
filtered. For contravariant families one would need common ancestors, which
rewriting does not give. Earlier parts of the conversation were loose about
this.

## 3.5 Cost

Enriching in `[0,∞]` is wrong for the orthogonality machinery: its underlying
maps are only the cost-0 ones, so a cost-1 step is not a map at all.

The right base is **normed sets**: sets whose elements carry a cost in
`[0,∞]`, with costs adding under tensor. [MEMORY] This is a cosmos (Grandis;
Perrone and Tholen on normed categories). Forgetting cost gives Set; taking
infima gives `[0,∞]`.

- Items 1–9 of the definition use the underlying maps unchanged.
- **Cost of a computation**: the infimum over its traces of total step cost.
  Cost is subadditive, so `E` becomes a normed category. `E₀`, the cost-0
  part, is bookkeeping.
- **Complexity function**: given a size on probes, `f(n)` is the largest
  evaluation cost at size at most `n`.
- A translation with bounded cost distortion preserves `f` up to the usual
  equivalence, so a complexity class is an invariant of the presentation.
- Costs can live in any quantale (time and space together, for example).

Worked example: group presentations and the Dehn function, `04` §4.3.

## 3.6 Convergence and size

Item 4 is the size condition. What it buys is structural. With a terminal
object, convergence makes behaviours reflective: every description has a
denotation `LX` [LEAN: `Presentation.isRightAdjoint_of_convergent`]. It also
makes conversions the 2-out-of-3 closure of `E` [LEAN:
`Presentation.conv_le_of_E_le`].

An earlier version said convergence is *equivalent* to existence of the
reflector. Only one direction is shown. A reflector gives `X → LX → 1` with
`LX → 1` in `M`; whether `X → LX` is in `E`, and whether every other map
factors, needs the reflection to work in every slice. Open (`11` row 18).

- [CITED] This is Freyd and Kelly's orthogonal subcategory problem.
- [CITED] How definable the class of steps is decides the set-theoretic
  strength needed: provable in ZFC at the lowest level, large cardinals above
  (Bagaria, Casacuberta, Mathias, Rosický).
- [CITED] Mathlib has an orthogonal-reflection construction for a small class
  of maps, which is the iterated evaluation.
- The reflector is built by iterating a plus-construction ([CITED] Anel,
  Biedermann, Finster, Joyal for the general small-object/plus-construction
  picture). The size condition is convergence of that iteration.

**Three grades** [HAND]:

1. `L` exists: every description has a denotation.
2. Some trace has finite cost: weak normalization.
3. All traces have bounded cost: strong normalization with a bound.

`L y(t)` exists even when `t` has no normal form; it is then not representable
(`06` §6.5).

## 3.7 Dictionary

How earlier anchors appear.

| Anchor | In the framework |
|---|---|
| Normal form | `S`-local object; terminal object of its fibre |
| Normalization | Unit `X → LX` |
| Confluence | Ore condition of a calculus of fractions |
| Sheaves | `A` a site, `S` the covering sieves; `L` is sheafification, so sheafification is a normalization |
| Types as closed sets | Orthogonality to `S` is the doings-and-tests closure |
| Normalization by gluing | `A` = variables and renamings; glue along the nerve (Fiore's relative hom functor) |
| Realizability | `A` = partitioned assemblies, `Φ` = exact completion, `S` trivial; types are literally subquotients |
| Behaviour doctrines | `A` a path category; open maps lift path extensions |
| Cost | Normed sets; complexity is minimal trace cost |
| Holes | Homotopy of the reduction space; localize homotopically, keeping `S` as cells |
| Church–Turing | Top class under simulation in a fibre of the tower |
| Knuth–Bendix completion | Adding steps already in `E` |
| Denotational semantics | Change of base to Set |
| Coercion | Unique filler of a computation against a type family |

[CITED] "Normalization is localization" is a theorem in at least one setting:
"Presenting a category modulo a rewriting system" (RTA 2015) shows that for
convergent systems with coherence conditions, normal forms, the quotient and
the localization agree, via a calculus of fractions.
