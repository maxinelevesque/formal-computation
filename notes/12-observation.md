# 12. Observation as an ingredient (proposal, 2026-11-19)

Status: a proposal for discussion. Labels as in `README.md`; [LEAN] marks what is already
proved, [LEAN-next] what would be formalized if the proposal is accepted.

## 12.1 Where things stand

- **The essay** gives a presentation three ingredients: descriptions, steps, observation. Its
  observation is built from descriptions. A probe is a context, the outcome is run, and the
  probe reads only what it supplied. The answer is a term or nothing.
- **The formal definition** (`notes/03`, Lean) has two: a category of descriptions and a
  class of steps. Behaviours are determined by the steps alone. The kind of answer is fixed
  (sets), and probes do not appear.
- **The essay's sentence that already bridges them:** "Steps settle which predicates are
  types. Probes are the usual way of defining one." [LEAN: `isType_probePred`,
  `runsToI_not_probe`]

The intuition to test is that observation made from descriptions is a well-behaved special
case of something more general.

## 12.2 The proposal: observers are families, observation is evaluation

Take the dynamic picture: `A` is the category of descriptions and runs, and a family is a
functor `A → Set`. Observing a description `t` with a family `X` means evaluating it, `X(t)`.
By Yoneda this is the hom pairing `Hom(y t, X)`. So the general ingredient is:

> An **observation** is a class `𝒪` of families, the observers. Two descriptions are the
> same under `𝒪` when evaluation at them agrees on `𝒪`: `ev_t ≅ ev_u` as functors on the full
> subcategory spanned by `𝒪`.

A presentation then has three ingredients, matching the essay: descriptions (`A`, or `P`
via Yoneda), steps (`S`), and observers (`𝒪 ⊆ P`). The observers are contravariant to the
descriptions. Larger classes of observers give finer equalities: a Galois connection
between classes of observers and equivalence relations on descriptions.

**The essay's three equalities are three classes of observers** [HAND; LEAN-next]:

| Observers `𝒪` | Sameness under `𝒪` | Why |
|---|---|---|
| all families | sameness of text (`t ≅ u` in `A`; in a free category of runs, `t = u`) | Yoneda in `[A, Set]` |
| all behaviours | sameness after running (`t ≅ u` after inverting the steps: one fibre) | Theorem A, then Yoneda in `[A[S⁻¹], Set]` |
| probe-defined types | sameness under probes | each probe gives a subsingleton family; evaluation agrees iff every probe reads alike |

Each class contains the next, so each equality is coarser than the one before, which the
essay states and illustrates but does not explain. On this account it is the order-reversal
built into observation. Probes that read code give a class between the last two (still
inside behaviours) [LEAN: `codeEq_iff_conv`].

Behaviours, in this language, are exactly **the observers that cannot see direction**:
families that send each step to a bijection [LEAN: `beh_iff_map_bijective_co`]. That was
the slogan proposed for the variance decision. Here it becomes the dividing line between
classes of observers.

## 12.3 What makes the essay's case well behaved: four properties

The essay's probes have four properties at once. Each can fail on its own. Each is stated
here by what it buys, and by which of the essay's cards drops it.

1. **Invariance**: every observer is a behaviour (`𝒪 ⊆ Beh`).
   - *Buys:* running implies observation; sameness under `𝒪` is coarser than sameness after
     running [LEAN, for probes: `probeEq_of_conv`; in general a one-line consequence of
     Theorem A]. Observers factor through the localization.
   - *Fails for:* the cost card (a probe that returns a cost sees how many steps were taken,
     so a step changes the reading) and the card on watching a run (traces, bisimulation).
     These observers can see direction. For cost the natural answers are lengths, in
     Lawvere's sense: a step acts by an inequality, not a bijection. The equality they give
     is not coarser than running.
2. **Internality**: observers are made from descriptions. There is an action of contexts on
   descriptions, a small set of reading families `R`, and `𝒪 = { C*R }` (put the term in the
   context, then read).
   - *Buys:* sameness under `𝒪` is a congruence [LEAN, for probes: `probeEq_plug`], and
     questions of full abstraction make sense.
   - *Fails for:* the essay's figure "one probe, two calculi". There the observer belongs to
     neither calculus and is reached through encodings, so it is external. Comparison then
     needs a span of translations into a common observer, which is where Theorem B
     (simulations as adjunctions) should enter.
3. **Abstraction**: a reading family sees only what the observer supplied.
   - *Buys:* the gap between probes and running, which is where extensionality lives.
   - *Dropping it* (reflection, reading code) collapses observation onto running for terms
     with a value [LEAN: `codeEq_iff_conv`, `not_codeEq_I_SKK`]. This is the card "a probe
     may read code".
4. **Kind of answer**: readings in a set.
   - *Varies to:* yes/no (types), lengths (cost), proofs with their own equalities (the card
     on dependent types), sets of offers (processes). Changing it changes what a behaviour
     is: `V`-valued families that send steps to invertible maps of `V`.

The well-behaved special case is 1–4 together: invariant, internal, abstract, set-valued.

## 12.4 Generalizations this opens [SPEC unless marked]

- **Directed observers.** Families with non-invertible step action, valued in an ordered or
  enriched `V`. Cost is the basic example. The framework's own invariants (the weight on SKI
  runs, the ℤ-valued behaviour on the pentagon) sit at the boundary: invariant along steps,
  but not determined by the endpoints of a run.
- **Watching runs.** Joyal, Nielsen and Winskel define bisimulation by open maps: lifting
  against extensions of path shapes [CITED in the essay]. Observation of runs is then again
  orthogonality, now against path extensions instead of steps. If this holds up, the process
  card is a presentation whose observers are path shapes, and its equalities come from a
  factorization system as behaviours do.
- **External observation and translation.** An observer category `Q` with a functor from
  descriptions, or a span of translations into `Q`. The Church–Turing comparison in the
  essay is of this kind: observers are numerals in, numerals out.
- **Pairings.** Elementarily, an observation is a pairing `⟨d, o⟩ ∈ V` between descriptions
  and observers, natural along runs: a Chu space over `V` (Pratt). With `V = 2` it is a pole
  in Krivine's sense, and biorthogonally closed sets are the types of realizability, which
  the essay already cites (Pitts; Vouillon–Melliès). For invariant poles, biorthogonal sets
  are types in the essay's sense [HAND, easy; LEAN-next].

## 12.5 What changes if this is adopted

**Formal definition (`notes/03`, `SUMMARY.md`).** A presentation becomes `(P, S, 𝒪)`.
Everything proved so far is the case where `𝒪` plays no role (behaviours) or is a class of
behaviours (probes). Nothing proved is invalidated.

**Lean** [LEAN-next]:
- `Observation`: a class of families. `ObsEq`, defined as agreement of evaluation on the
  full subcategory.
- The three-classes theorem:
  - `ObsEq (all) ↔ iso in A`, by Yoneda;
  - `ObsEq (Beh) ↔ iso in A[S⁻¹]`, by Theorem A and Yoneda;
  - `invariant ⇒ Conv ≤ ObsEq`.
- The SKI probe observation as an instance, with `ProbeEq ↔ ObsEq` over the SKI run
  category. This needs the run category as a Lean category (`Paths Tm`) and each probe
  reading as a functor; forward closure of `Reads` follows from confluence.
- Biorthogonal types are types, for an invariant pole.

**Essay.**
- The definition section would say observers are families, and that the essay's probes are
  the well-behaved case, naming the four properties.
- The three equalities would be read as three classes of observers. A small figure would
  help: nested observer classes against nested equalities.
- The cards would sort by which property they drop: invariance (cost, watching runs),
  internality (comparison of calculi), abstraction (reading code), kind of answer (proofs,
  processes).

## 12.6 Decisions (2026-11-19)

1. **Pairing first, families as a special case** (Maxine). An observation is a pairing
   `pass : D → O → Prop` between descriptions and observers. A class of families is the
   special case `pass t B := B t is inhabited`. [LEAN: `Obs.Pairing`, `Obs.familyPairing`,
   `Obs.familyPairing_invariant`] Truth-valued for now. Cost and other directed observers
   want pairings valued in an ordered `V` (a Chu space over `V`), which is §12.8.
2. **Where the classification goes**: proposed, awaiting Maxine. In "Atoms and Probes",
   one sentence in the definition (observation is any pairing, and the essay studies probes)
   and the cards sorted by which of the four properties they drop. The theory (pairings,
   lenses, the three-classes theorem, directed observers) goes to the technical companion.
3. **Directed observers**: discussed in §12.8; proposed as a section of the technical
   companion, not of the essay.

The questions as first asked:

1. Observers as families, internal to `P` via Yoneda; or observation as an independent
   pairing (Chu space / pole)? The proposal takes families, with the pairing as the
   elementary picture in the essay. The pairing is more general (observers need not be
   families of the same calculus); families keep everything inside the framework and make
   Theorem A apply.
2. Should the essay carry the four-properties classification of its cards, or keep it for
   the second post?
3. Directed observers (cost, traces) are where "observation can see direction" lives. Is
   that the meeting point of algebra-like and coalgebra-like you were after? If so it may
   deserve its own section.

## 12.7 Types built from lenses

The question comes from Zya's setting. To show that a predicate is a type, one must show
that no step changes it, which quantifies over every term and every step. Zya moved to types
built by composing lenses. The pairing gives a construction of that kind here.

- **Types as tests.** For a set `T` of observers, `T^⊥` is the set of descriptions that every
  observer in `T` accepts. If the pairing is invariant, every `T^⊥` is a type.
  [LEAN: `Obs.Pairing.orth_invariant`; for SKI `SKI.isType_orth`, where invariance is
  confluence, `SKI.probes_invariant`] A probe type is the case of one test.
  [LEAN: `SKI.probePred_iff_mem_orth`]
- **Lenses.** A lens from `(D, O)` to `(D', O')` sends descriptions forward (`get`) and
  observers back (`put`), so that an observer sent back gives the verdict it gives
  forward: `pass d (put o') ↔ pass' (get d) o'`. This is a morphism of Chu spaces. Lenses
  compose. [LEAN: `Obs.Lens.comp`]
- **Lenses pull types back to types**: `get⁻¹(T^⊥) = (put T)^⊥`. [LEAN:
  `Obs.Lens.preimage_orth`] A type built by composing lenses down to a set of tests is
  therefore a type with no proof of its own. The obligations are:
  - one invariance proof for the pairing;
  - one equation per primitive lens, which for contexts is a computation
    (`Probe.plug_subst`).

  Nothing is enumerated per type.
- **Example.** "Apply to `a`" is a lens. Forward it sends `t` to `t a`; back it sends `C` to
  `C[[ ] a]`. [LEAN: `SKI.applyTo`] Arrow types are built from these lenses: if
  `B = T^⊥`, then `A → B = (⋃_{a ∈ A} put_a T)^⊥`, for any predicate `A`. [LEAN:
  `SKI.arr_iff_mem_orth`] The probe `[ ] x y` is the composite of two such lenses.
- **Lenses carry sameness forward.** [LEAN: `Obs.Lens.same`] When the lenses are contexts,
  this is the statement that sameness under the observation is a congruence. It is the
  general form of `SKI.probeEq_plug`.
- **The limit.** Lens-built types are exactly as fine as the observers. Over probes they
  cannot see code: "runs to `I`" is a type but not a probe type
  (`SKI.runsToI_not_probe`). Whether this is a defect or the point depends on what the
  types are for. With observers that read code, lens-built types reach it.
- **Closure.** `T ↦ T^⊥` turns unions of tests into intersections of types [LEAN:
  `Obs.Pairing.orth_iUnion`], and `S ↦ S^⊥⊥` gives the smallest lens-built type
  containing a set `S`. Unions of types need this closure, as in realizability. [HAND]
- **Prior art.** Now checked; see `notes/13` §13.B for DOIs and what was read. The nearest
  is Klin (CMCS 2010): Chu(Set, 2) = (Set↓2^−), whose morphisms are exactly our lenses.
  Our `put` is single-valued because observers are contexts; the modal-decomposition
  line (Fokkink–van Glabbeek–de Wind 2006) needs sets of decompositions. Earlier list:
  - Chu spaces: Pratt.
  - Biorthogonality and ⊤⊤-closure: Pitts, *Parametric polymorphism and operational
    equivalence* (MSCS 2000); Vouillon and Melliès, *Semantic types: a fresh look at the
    ideal model for types* (POPL 2004); Krivine's realizability.
  - Proof-relevant version: de Paiva's Dialectica categories and dependent lenses. There
    `put` may depend on the description, `put : (d : D) → O' → O_d`. This is the step to
    take when observers return evidence rather than a verdict.
- **Caveat.** This is a reconstruction from "types as predicates built from composing
  lenses". The lenses here need only the adjointness equation, not the get–put laws of
  bidirectional programming. Whether it matches Zya's construction needs her setting.

## 12.8 Directed observers, algebra and coalgebra [SPEC unless marked]

**Update (2026-11-19).** `notes/13` corrects this section. Bisimulation as lifting with
existence only is known: Joyal–Nielsen–Winskel, Kurz–Rosický, Hirschowitz–Lafont. What
remains ours is the orthogonal half in the same category of runs, and the observation that
the halves coincide for deterministic reduction (§13.0, §13.C).

- **Invariant observers give algebra.** A behaviour sends each step to a bijection
  [LEAN: `beh_iff_map_bijective_co`]. The equality it gives is a quotient of descriptions
  by conversion: what a description equals. This is the algebraic side: equational
  theories, initial-algebra semantics, the localization of Theorem A. All three of the
  essay's equalities are on this side.
- **Directed observers give coalgebra.** A step acts on a directed observer by a map that
  need not be invertible. Examples:
  - the runs out of `t`, where a step `t → t'` sends each run out of `t'` to a run out of
    `t` by prefixing; it is not onto, because `t` has runs that do not pass through `t'`;
  - traces;
  - cost, valued in Lawvere's `([0, ∞], ≥)`, where a step acts by an inequality.

  The equalities these give are behavioural: bisimilarity, trace equivalence, cost
  equivalence. They say what a description does as it runs. This is the coalgebraic side:
  transition systems, final-coalgebra semantics.
- **The meeting point.** Turi and Plotkin, *Towards a mathematical operational semantics*
  (LICS 1997) [MEMORY]. Rules in the GSOS format are a distributive law of syntax over
  behaviour. Bisimilarity is then a congruence, and the semantics by initial algebra and
  by final coalgebra agree. In the language of §12.3 this is **internality** (observers
  made from contexts) together with **direction**. `Obs.Lens.same` and
  `SKI.probeEq_plug` are the invariant case of that congruence theorem.
- **A structural guess.** Invariance is *unique* lifting against steps, the orthogonality
  that the framework is built on. Bisimulation by open maps (Joyal, Nielsen and Winskel,
  *Bisimulation from open maps*, Inf. & Comp. 1996 [MEMORY]) is lifting with *existence
  only*, against extensions of paths. If this holds, algebra and coalgebra appear as unique
  and non-unique lifting against two classes of maps in one category of runs. Algebra is
  an orthogonal factorization system on steps; coalgebra is a weak factorization system
  on path extensions. The lax theory, open problem 1 in `SUMMARY.md`, would sit between
  them. Not checked: whether the open-map lifting lives in the same category as the
  framework's lifting, or one level up.
- **Where it goes.** A section of the technical companion, "Observers that see
  direction". The essay keeps its cards on cost and on watching runs as they are.
