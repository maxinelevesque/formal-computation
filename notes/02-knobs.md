# 2. The knobs

The space of "notions of computation" is organized by four parameters. They
form a tower, not a product: each makes sense only once the ones below are
fixed. The assembly into one structure is ours [SPEC]; each coordinate is
established on its own.

## 2.1 Enrichment: what a probe returns

Fixing the enriching category `V` fixes what kind of object a fibre is.

| `V` | A probe returns | A fibre is |
|---|---|---|
| Sierpiński truth values | "it halted" (yes only) | a reachability preorder |
| Costs | a cost | a directed metric space |
| Probabilities | a probability | (probabilistic coherence spaces) |
| Sets | the set of ways of passing | a category |
| Spaces | a homotopy type | an (∞,1)-category |
| Presheaves over time | "holds for n more steps" | step-indexed |

Notes.

- The classical choice is Sierpiński space, not Boolean 2. You can see "it
  halted" but never "it won't". That asymmetry is where the topology of
  computation comes from.
- [MEMORY] Danos and Ehrhard's probabilistic coherence spaces are closed-set
  types for a pairing valued in non-negative reals.
- [MEMORY] Step-indexing in the topos of trees: Birkedal and coauthors.
- [MEMORY] Laird, Manzonetto, McCusker and Pagani's weighted relational models
  give a single construction parametrised by a semiring: Booleans give
  may-convergence, naturals count reduction paths, the tropical semiring gives
  minimal cost, non-negative reals give probability. This is a true family
  over the knob.
- [CITED] Baez and Williams: change of base graphs → categories → posets →
  sets takes small-step to big-step to full-step to denotational semantics.
- **Correction** (`03` §3.5). For cost, the right base is normed sets, not
  `[0,∞]`. In `[0,∞]` the underlying maps are only the cost-0 ones.
- **Addition** (`03` §3.3). Insert spaces between categories and sets:
  Cat → spaces → Set. Squier-type invariants live on the middle rung.

**Structural sub-knobs** of `V`.

- Cartesian or merely monoidal: whether observations can be copied and
  discarded. If not: linearity, resource sensitivity.
- Symmetric or not: whether the order of probing matters.
- Dualizing object or not: whether doings and tests are on equal footing
  (linear logic) or asymmetric (intuitionistic logic).
- Thin, categorical or homotopical: whether evidence is a mere fact, a
  structure, or a structure with holes.

**Home turf.** [MEMORY] Walters (early 1980s): sheaves on a site are
Cauchy-complete categories enriched in a bicategory. So the object of
observations need not be global; it can vary with context. Enrichment in a
bicategory or virtual double category is the natural general setting, with
Cauchy completeness playing the role of gluing.

## 2.2 Probe shapes: the behaviour doctrine

**A behaviour doctrine is a choice of probe shapes in time.** It is the same
Yoneda move as the base, applied to runs.

**The core.** Pick a category of path shapes: what a run can look like and how
shorter runs extend to longer ones. A behaviour type is a presheaf on it. A
system is a bundle over it with a path-lifting property. [MEMORY] Joyal,
Nielsen and Winskel 1996: open maps are those that lift paths, bisimulation is
a span of open maps, and the path category is the parameter. Linear sequences
give transition systems; partially ordered runs give true concurrency.

A deterministic system is literally a covering of the category of runs: a
discrete opfibration.

**How the usual ingredients fit under this.**

- **Step functor.** It generates the path category. [MEMORY] In Spivak and
  Niu's polynomial setting, the cofree comonoid on an interface is a category
  of runs, and systems on that interface are copresheaves on it. Coalgebraic
  examples: step-or-stop (the Turing-style run), output-and-continue
  (streams), branch on labelled moves (processes), move by a distribution
  (Markov).
- **Shape of time.** The path category chosen directly: a monoid, or a site of
  intervals ([MEMORY] Schultz and Spivak's temporal type theory).
- **Effects and branching.** These are the lifting condition: unique, merely
  existing, or weighted. That is the enrichment coordinate again. [MEMORY]
  Hasuo, Jacobs and Sokolova separate a branching monad from a linear-time
  step functor. Moggi's "notions of computation as monads" is the same point.
- **Built versus probed.** Variance. Initial algebras are defined by how they
  are constructed; final coalgebras by how they respond to observation.
  Colimits of probes sit on one side of Isbell duality, limits of observations
  on the other. Call-by-push-value makes the split an adjunction between value
  types and computation types. This polarity returns in `07` §7.3.
- **Openness.** Path shapes carry a second composition, in space, by plugging
  interfaces together. Two compositions with interchange make a double
  category. [MEMORY] The Turi–Plotkin distributive law of syntax over
  behaviour is that interchange: a step of a composite is determined by steps
  of its parts, so bisimilarity respects composition. [CITED] Goncharov et al.
  extend this to higher-order languages.
- **Concurrency.** In directed topology, independent actions fill in a square,
  and holes in the state space are real conflicts such as mutual exclusion.
- **Minimal realization.** A system sits between free syntax and total
  behaviour; the normal form generalizes to the minimal realization (minimal
  automaton, Kalman's minimal realization).

[CITED] Myers' categorical systems theory, and Libkind and Myers' double
operadic theory, are the closest formal version: systems as a module over a
double category of interfaces, with behaviours representable.

So: enrichment says what a probe returns; the behaviour doctrine says what
shape probes have, in time and in space.

## 2.3 Arities: which probes are small

Probe shapes and smallness are one datum: a pair `(A, Φ)`, a category of
probes and a class of colimit weights. The terms are `Φ(A)`, the free
completion of `A` under `Φ`-shaped gluings.

- [CITED] This is the standard setting: Bourke and Garner's "Monads and
  theories" starts from a small dense subcategory of arities in a locally
  presentable enriched category. Earlier: Weber; Berger, Melliès and Weber.
- `Φ` runs from the absolute weights up to all weights. The absolute end gives
  Cauchy completion. Absolute weights are exactly the dualizable ones. So
  "finite as dualizable" (`01` §1.7) is the minimal setting, with no cardinals.
- [CITED] Lack and Tendas and collaborators replace cardinals by a "sound"
  class of weights and rebuild presentability and accessibility over it.
- Other choices already in use: Kleene's second algebra uses infinite streams
  as realizers; continuity replaces finiteness.
- In normalization proofs the probes are variables and renamings, not all
  substitutions (`07` §7.5).

**What must survive.** Some smallness constraint. If probes are unrestricted,
every map is computable and the fibres go flat: no complexity, no
undecidability, only semantics. The gap between small probes and what they
generate is where the content lives.

## 2.4 Self-classification

Reflexivity, structurally, says the bundle contains its own classifying
object.

- It is a property of an object in a fibre of the tower, not a base
  coordinate: does the model contain a classifier for its own small things?
- Type-in-type gives Girard's paradox, which gives looping terms. A universe
  hierarchy is the stratified, tame version.
- In dependent type theory the classifier of types is what makes type formers
  stable under substitution (`07` §7.4).
- Tree calculus achieves self-classification at the level of values, with no
  encoding, and pays with partiality (`04` §4.6).

## 2.5 The tower

1. **Enrichment** `V`. Change of base moves everything above.
2. **Probes and arities** `(A, Φ)`, enriched in level 1. A map of probe
   categories gives restriction and Kan extension between behaviour worlds.
3. **Models**: presentations over a choice of 1–2 (`03`).

Self-classification is a property of objects at level 3.

**The object** at the top is a pairing between doings and tests, valued in `V`
and shaped by `A`. Equivalently a nerve–realization adjunction between small
things freely glued together and the behaviours they denote. The realization
map is the internal bundle.

**Morphisms** come in two kinds, making the total structure a double category
(`05`).

**Classification.** A Church–Turing thesis is a statement that a fibre of the
tower has a single top class under simulation. It holds in the classical fibre
for functions ℕ → ℕ and fails at higher types. For most knob settings no
answer is known to us. [SPEC]

**Templates that come close.**

- [MEMORY] Institution theory (Goguen and Burstall): a satisfaction pairing
  between models and sentences, fibred over signatures, flattened by a
  Grothendieck construction.
- [MEMORY] Uemura's framework: a type theory as a category with a class of
  representable maps, which is smallness as a class of bundles.
- [CITED] Baez and Williams: a Grothendieck construction collecting all models
  of all enriched Lawvere theories over all bases.
- [CITED] Longley: a 2-category of computability structures and simulations.

Where higher coherence calms down is in `09`.
