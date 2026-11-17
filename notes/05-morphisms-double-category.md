# 5. Morphisms and the double category of presentations

Fix `V = Set`. Presentations are `(A, S)` with `P`, `E`, `M`, `C`, `L` as in
`03`. Write `Conv` for the conversions (maps inverted by `L`).

## 5.1 Translations and simulations

- A **translation** `(A, S) → (A′, S′)` is a functor `F : A → A′` whose left
  Kan extension `F_! : P → P′` sends `S` into `E′`.
- A **simulation** is any cocontinuous functor `G : P → P′` (equivalently a
  profunctor from `A` to `A′`) with `G(S) ⊆ E′`.

A translation is a representable simulation. A step is allowed to go to a
composite computation, so compilers are translations when the encoding is
functional.

## 5.2 Theorem B

> **Lemma** [HAND]. Let `G ⊣ R` with `G : P → P′`, and suppose `G` sends every
> step of `S` to a conversion of `S′`. Then `R` sends `S′`-local objects to
> `S`-local objects.

*Proof.* For `s : X → Y` in `S` and `Z` local for `S′`, precomposition with
`s` on `Hom(–, R Z)` transposes to precomposition with `G s` on `Hom(–, Z)`,
which is a bijection because `G s` is a conversion and `Z` is local. ∎

Only conversions are needed, not computations.

> **Theorem B** [HAND]. A translation or simulation induces an adjunction
> `C ⇄ C′`: the right adjoint is the restriction of `R`, and the left adjoint
> is `L′ ∘ G` on `C`.

Consequences, all [HAND]:

- **Saturation.** The preimage of `E′` under `G` is saturated and contains
  `S`, so `G(E) ⊆ E′`.
- **Composition.** Translations and simulations compose; presentations form a
  category in each direction.
- **Completion is harmless.** If `S ≤ S′ ≤ Conv(S)` then the local objects
  agree. Adding rules already in `E` changes neither `E` nor `C`. This is why
  Knuth–Bendix completion is harmless.
- **Reversed rules.** Adding the inverse of a step keeps `C` and changes `E`:
  the same denotations with different computations.
- **Uniting rule sets.** The local objects for `S₁ ∪ S₂` are the intersection
  of those for `S₁` and `S₂`.

## 5.3 The double category

Translations are **tight** and simulations **loose**; squares are natural
transformations. Presentations form a double category.

**Companions and conjoints** [HAND].

- Every translation `F` has a companion: the pushforward `F_!` is a
  simulation by definition.
- `F` has a conjoint only when restriction `F^*` also preserves computations,
  that is `F^*(S′) ⊆ E`. This is a step-lifting condition: every step at an
  image lifts to a computation upstairs. Coverings (discrete opfibrations)
  satisfy it, since a step pulled back along a covering is a disjoint union of
  lifted steps.
- So the double category fails to be an equipment exactly where simulation
  differs from bisimulation.

**Adjoint triples** [HAND]. If `F` has a conjoint, restriction along `F` on
behaviours has both a left and a right adjoint. In the dynamic picture this is
the adjoint triple for local systems along a covering map.

**A recurring pattern.** Strict maps embed into weak ones through companions;
going back is a strong extra condition. The same pattern appears for
definitional and propositional equality (`07` §7.5).

## 5.4 Abstract interpretation [SPEC]

The induced adjunction between behaviour categories reads as abstraction and
concretization. Soundness is the translation condition. Completeness looks
like the conjoint condition. Not checked against the abstract-interpretation
literature.

## 5.5 Descent and van Kampen [HAND]

Uniting rule sets on the same probes is a pushout of presentations.

- **Behaviours** take it to an intersection: `C(S₁ ∪ S₂) = C(S₁) ∩ C(S₂)`. So
  behaviours satisfy descent for covers of the rule set.
- **Reduction groupoids** take it to a pushout: localizing at `S₁ ∪ S₂` is the
  pushout of the localizations at `S₁` and `S₂` over `A`.
- **Critical pairs** are the new loops in the amalgam: loops that use both
  rule sets and exist in neither piece.

This makes the Čech analogy of `04` §4.2 precise at level 1.

## 5.6 Parallel composition [HAND]

The product of presentations `(A × A′, S × 1 ∪ 1 × S′)` has the product
reduction category. So π₁ multiplies and cost adds. Behaviours of the product
are the tensor of behaviours. The double category is monoidal.

Read this way, interchange is independence, and holes measure interaction:
the failure of a presentation to decompose as a product of its rules'
presentations. Mutual exclusion in concurrency is the same phenomenon.

## 5.7 Three classes of morphism, three theses

A translation or simulation may send steps to

1. **conversions** (denotational): enough for the adjunction on behaviours;
2. **computations** (operational): the definition in §5.1;
3. **computations with bounded cost** (complexity-preserving), over normed sets.

These give nested sub-double-categories.

[SPEC] The theses line up with them.

- **Church–Turing** is weak terminality in the operational class, in the
  loose direction. Encoding into a universal machine is typically a simulation
  (many codes for one term; steps up to conversion), not a translation.
- **Extended Church–Turing** is the same statement in the cost-bounded class.
  This is where quantum computation is conjectured to differ.
- **Jay and Vergara's objection** [CITED] is that the thesis conflates mutual
  simulation with equivalence. In these terms: maps exist in the loose
  direction both ways, but not in the tight direction (`04` §4.6).

## 5.8 A possible home [SPEC]

[CITED] Lambert and Patterson treat theories as cartesian double categories.
If "presentation" is a model of such a double theory (a category with a marked
class of maps is a simple case), then tight and loose maps come for free, and
their general theory applies.

## 5.9 Related formal work

- [CITED] Longley's 2-category of computability structures and simulations,
  where simulations correspond to functors between realizability models. This
  is the morphism layer without the enrichment or arity knobs.
- [CITED] Baez and Williams' Grothendieck construction over enriching bases.
- [CITED] Libkind and Myers: systems as modules over double categories of
  interfaces.
