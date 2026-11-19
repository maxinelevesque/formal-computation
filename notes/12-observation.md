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

## 12.6 Questions for Maxine

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
