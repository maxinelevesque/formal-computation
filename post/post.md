# Show me the holes: computation as a factorization system

*Draft, 2026-11-17. Every claim carries a status. **[LEAN]** means proved in
Lean 4 with Mathlib in the accompanying repository, with no `sorry` and no
axioms beyond Lean's standard three; the tag links to the declaration.
**[HAND]** means argued by hand and not mechanized. **[CITED]** and
**[MEMORY]** are published results, found by search or recalled. **[CONJ]**
is a precise conjecture, **[SPEC]** a speculation.*

---

## Part I. The short version

### 1. The question

What is computation, seen relationally? In computer science it is usually
treated as close to primitive: there are machines, they take steps, and the
interesting object is the function they compute. I want an account in which
categorical structure comes first, the set-like things are derived, and the
*form* of computation is visible without backing down to sets.

The intuition worth keeping is that computing means constructing a solution
from predefined structural primitives, and that how hard this is depends on
the construction, not only on the answer.

### 2. The answer in one paragraph

**Computation is a factorization system on descriptions; denotation is its
localization; holes show up as monodromy.** Anything given by a presentation
has many descriptions, and the descriptions form a space fibred over the
things they describe. Taking connected components recovers the denotation.
Computation is the directed geometry of the fibres, which taking components
forgets. The input–output function is the shadow; the fibre is the object.
This post makes that precise with one definition, two general theorems and
three worked examples, most of it checked in Lean.

### 3. The definition in ten lines

A **presentation** is a category `P` of descriptions and a class `S` of maps
in it, the **steps**. Everything else is derived.

1. `M` is the class of maps with *unique* right lifting against every step.
2. `E` is the class of maps with unique left lifting against `M`. These are
   the **computations**. Every step is one [LEAN][steps_le_E].
3. **Behaviours** are the objects `X` whose map `X → 1` is in `M`;
   equivalently, the objects that see every step as a bijection
   [LEAN][beh_iff_M].
4. **Conversions** are the maps that every behaviour sees as a bijection.
   Every computation is one [LEAN][E_le_Conv].
5. The presentation is **convergent** when every map factors as a
   computation followed by an `M`-map.
6. **Evaluation** of `X` is then the factorization `X → LX → 1`. The first
   map is the big step; `LX` is the denotation [LEAN][isRightAdjoint_of_convergent].
7. Under convergence the conversions are exactly what you get by closing the
   computations under 2-out-of-3 [LEAN][conv_le_of_E_le].
8. In the main example, `P` is presheaves on a category `A` of terms and
   reductions, a term `t` is described by `y(t)`, and the steps are the
   rewrites `y(t) → y(t′)` [LEAN][toPresentation].

**The model is the pair `(P, E)`, not the category of behaviours.** Keeping only
the behaviours throws away the direction.

### 4. The dictionary

| Rewriting notion | In the framework | Status |
|---|---|---|
| Normal form | A local object; a terminal object of its fibre | definition; [LEAN][rOrth_terminal_iff_isLocal] |
| Normalization | The unit `X → LX`, a conversion | [LEAN][unit_mem_Conv] |
| Coherence theorem | Every fibre contractible; behaviours are bare sets | [LEAN][beh_equiv_type_of_terminal] when there is a terminal term |
| Knuth–Bendix completion | Adding steps already in `E`: changes neither `E` nor behaviours | [LEAN][E_eq_of_le_of_le_E] |
| Confluence | Ore condition; calculus of fractions | [HAND], [CITED] for one setting |
| Coercion along a reduction | The unique diagonal filler | [LEAN][coerce] |
| Complexity | Minimal cost of a trace | [LEAN][cost_eq_area] for groups (cost = area) |
| Denotational semantics | Change of base to sets | [SPEC] |

### 5. What is proved, what is cited, what is conjecture

**Proved in Lean** (tiers 1–3 of the proof map; the axiom audit is in
`AXIOMS.md`):

- **Orthogonality and coercion.** The closure properties of `M`, coercion as
  the inverse of restriction, its strict functoriality, and transposition of
  orthogonality along adjunctions. [§13]
- **Theorem A.** Behaviours of the dynamic picture are local systems:
  presheaves on which steps act bijectively, equivalently functors out of the
  localization at the steps [LEAN][behEquivLocalSystems]. Also for covariant
  families [LEAN][behEquivLocalSystemsCo]. A terminal term makes behaviours
  bare sets [LEAN][beh_equiv_type_of_terminal]. [§8]
- **Theorem B.** A simulation (an adjunction whose left adjoint sends steps to
  computations) induces an adjunction between behaviour categories
  [LEAN][adjOnBeh]. Uniting rule sets intersects behaviours
  [LEAN][isLocal_sup]; adding derivable rules changes nothing
  [LEAN][isLocal_eq_of_le_of_le_conv]. [§12]
- **The collapse lemma** and its converse: lax orthogonality to a free rule is
  the same as having a unique arrow from redex to contractum
  [LEAN][lax_orthogonal_iff]. [§7]
- **Associativity.** Without the pentagon, the two routes around it stay
  distinct after inverting every reduction, and a behaviour tells them apart
  [LEAN][exists_beh_top_ne_bot]. [§9]
- **SKI.** A 1-cocycle on K-free reductions [LEAN][wt_permEq]; the loop at
  `Ω = SII(SII)` is not absorbed by any continuation [LEAN][not_absorbed];
  the loop inside `K a Ω` is [LEAN][absorbed]. [§10]
- **Groups.** Minimal trace cost equals area [LEAN][cost_eq_area]. [§11]

**Argued by hand, not checked:** that the reduction space of the free pentagon
is a circle and evaluation a ℤ-torsor; that the SKI loop has infinite order in
π₁ (this needs a calculus of fractions, see §10); translations via left Kan
extension and the double category of presentations; the Frobenius and
exactness conditions for dependent coercion; traces as pushouts of steps.

**Recalled or cited, not checked:** that imposing the pentagon gives the
Tamari order with coherence (Laplaza); that the permutation equivalence in
Lean is Lévy's; Clementino and López Franco's definition of lax
orthogonality; the cost and complexity facts about Dehn functions.

**Open:** the lax theory (§15), whether convergence is *equivalent* to the
existence of evaluation (§7), and the rest of §15.

---

## Part II. The detail

### 6. The motif

**Computation is composition with its bookkeeping left in.** In a category,
`g ∘ f` simply is. Anything given by a universal property or a presentation
is given only implicitly: one thing has many descriptions, and composing two
descriptions yields a formal juxtaposition, not an answer. So descriptions
form a space fibred over what they describe. Denotation is π₀ of that space;
computation is the directed geometry of the fibres, which π₀ forgets.

Three things fall out of this picture [HAND].

- **Where the moves come from.** A basic step is a constructor meeting its
  destructor: an introduction followed by an elimination, a zigzag of unit and
  counit held as a directed 2-cell instead of an equation. β-reduction and cut
  elimination are that one gesture ([MEMORY] Seely 1987 reads β and η as the
  counit and unit of a lax adjunction).
- **What a value is.** A normal form is a terminal object in its fibre: the
  description that wears its identity on its face.
- **What complexity is.** Running cost is distance travelled in a fibre. The
  difficulty of a construction is the size of the cheapest cell filling a
  given boundary. For groups this is literal (§11).

**The gauge analogy, and where it breaks.** A physicist's reading of gauge
theory: the descriptive apparatus is too floppy for the thing described, so
descriptions carry redundant structure, studied in order to be quotiented
out. Computation has the same shape, and the modern form is to resolve rather
than quotient: a presentation with its rewrites, and rewrites between
rewrites, is a cofibrant resolution of the real thing ([CITED] polygraphs are
the cofibrant objects of the folk model structure on strict ω-categories).
The analogy breaks in two instructive places [HAND]. The fibres are
*directed*: orientation is extra data, not gauge. And cost is not pure
gauge: it behaves like holonomy, surviving change of presentation up to
coarse equivalence. The holes in §9 and §10 are where the directed structure
does work that an undirected one cannot.

### 7. The definition and why it has this shape

**First attempt.** Take a category of descriptions and a class `S` of steps,
and call the behaviours the objects orthogonal to `S`: those that see each
step as a bijection. This already matches a lot: sheaves are the objects
orthogonal to covering sieves, and normal forms are local objects. But
orthogonality *inverts* the steps. Direction survives only in the list `S`.

**The obvious repair, and why it fails.** Keep each rule `l ⇒ r` as a 2-cell
and ask models to accept it *laxly*. A model of a rule is a category `X` with
functors `l, r : Xⁿ → X`, the two sides of the rule. Adjoining a free 2-cell
`l ⇒ r` is a co-inserter, and a model of the rule together with its 2-cell is
an object of the **inserter** `Ins(l, r)`: arguments `a` and an arrow
`φ : l(a) → r(a)`, "how this instance reduces". Forgetting `φ` gives
`U : Ins(l, r) → Xⁿ`. Strict orthogonality would ask `U` to be an
isomorphism. Lax orthogonality asks for a best choice: a section
`a ↦ (a, ρₐ)` that is left adjoint to `U` with identity unit. That this is
Clementino and López Franco's notion is [HAND]; it is a citation check that
Lean cannot do.

> **Collapse lemma** [LEAN][collapse]. If the section given by `ρ` is left
> adjoint to `U` with identity unit, then for every `a`, `ρₐ` is the *only*
> arrow `l(a) → r(a)`.

The proof is one line. The adjunction says every `u : a → a′` is a morphism
`(a, ρₐ) → (a′, φ′)`, whatever `φ′` is. Take `a′ = a` and `u = id`: then
`ρₐ = φ′` for every `φ′`.

So laxness, meant to make room for structure, forces every hom-set
`X(l a, r a)` to have exactly one element. A lax-orthogonal model cannot hold
two different reductions of `I (I a)`, and cannot hold the proof-relevance
that SKI and the pentagon depend on.

The collapse is not an artefact of a convention, and three checked facts show
it.

- **It is a characterization.** For a natural `ρ`, the section is a left
  adjoint with identity unit *exactly when* every `X(l a, r a)` is `{ρₐ}`
  [LEAN][lax_orthogonal_iff], and then `U` is an equivalence
  [LEAN][forget_isEquivalence_of_unique]. Naturality of `ρ` is what makes the
  converse work: uniqueness at each `a` alone does not make the squares
  commute, because those live in `X(l a, r a′)`.
- **The side and the strictness do not matter.** The same collapse happens
  with an invertible unit instead of an identity [LEAN][collapse_of_isIso_unit],
  and with a right adjoint section with invertible counit
  [LEAN][collapse_of_isIso_counit].
- **A perfectly good model fails it.** Interpret the I-rule on types by
  `I = (– × Bool)` with `ι` the first projection. The two reductions of
  `I (I a)` differ: one drops the outer Boolean, the other the inner one
  [LEAN][accident]. So this model is not lax orthogonal to the I-rule
  [LEAN][not_lax_orthogonal].

**Conclusion.** Rule cells are structure, not property. Direction has to live
in a *class of maps*, not in a property of each model. That is the definition
in §3: the steps generate a factorization system `(E, M)`, the computations
are `E`, and the model is the pair `(P, E)`.

**What survives** [HAND]. The collapse is about *free* rules. Rules that are
units or counits of adjunctions, such as β and η, are universal 2-cells: there
can be many 2-cells from redex to contractum, but the rule is canonically the
best one, which is exactly the lax-idempotent situation lax orthogonality was
designed for. The dividing line between free rules and universal rules is the
bridge to type theory, which is for a second post.

**What the size condition buys.** Convergence (every map factors) is the one
size condition in the definition, and it is there for two reasons, both
proved. With a terminal object it makes behaviours reflective, so every
description has a denotation `LX` [LEAN][isRightAdjoint_of_convergent]. And it
makes conversions the 2-out-of-3 closure of computations
[LEAN][conv_le_of_E_le]. Conversions are then exactly the maps evaluation
inverts [LEAN][conv_iff_isIso_L]. Whether a presentation is convergent is
Freyd and Kelly's orthogonal subcategory problem [CITED]; how definable the steps are decides
how much set theory it takes ([CITED] Bagaria, Casacuberta, Mathias,
Rosický). An earlier draft said convergence is *equivalent* to the existence
of the reflector. Only one direction is proved: a reflector gives
`X → LX → 1` with `LX → 1` in `M`, but whether `X → LX` is a computation, and
whether every other map factors, is open.

### 8. Theorem A: behaviours are local systems

**Setting.** The dynamic picture takes the probes to be the terms themselves.
`A` is a category of terms and reductions; the steps are a class of maps in
`A`, the rule instances. Descriptions are presheaves on `A`; the term `t` is
described by `y(t) = A(–, t)`, and a step `s : t → t′` appears as
`y(s) : y(t) → y(t′)` [LEAN][toPresentation].

**Two variances.** Computation is covariant: `y(s)` moves the description
forward. Observation is contravariant: by Yoneda, an observation of `y(t)`
by `Z` is an element of `Z(t)`, and a step acts on observations by
`Z(s) : Z(t′) → Z(t)`, from the reduct back to the redex. Whatever `Z` says
about the reduct, it also says about the redex. A behaviour is an observer
for which that map is a bijection.

> **A1** [LEAN][beh_iff_map_bijective]. A presheaf `B` is a behaviour exactly
> when every step acts on it bijectively: `B(s) : B(t′) → B(t)` is a
> bijection for every step `s : t → t′`.
>
> **Theorem A** [LEAN][behEquivLocalSystems]. Behaviours are equivalent to
> functors out of the localization at the steps: local systems.

The proof goes in two moves. A1 is Yoneda, together with the observation that
locality does not see which arrow-isomorphic copy of a step one uses. Then
presheaves inverting the steps are, by the universal property of
localization, functors out of the localization [LEAN][behEquivInverting].
No size hypothesis is needed for Theorem A itself: the localization is
constructed from paths, and the theorem is an equivalence of categories of
presheaves.

**Behaviours cannot see direction.** On a behaviour, every step acts
invertibly, so the variance has nowhere left to live. When the steps generate
`A`, the localization is a groupoid, isomorphic to its opposite, and the
behaviours of the covariant presentation agree with these [HAND]. The
covariant version of Theorem A is proved separately [LEAN][behEquivLocalSystemsCo].
In the covariant category `A ⥤ Type` the step map runs
`Hom(t′, –) → Hom(t, –)`, from contractum to redex, so computations there
point backwards. That presentation is the natural one for type families and
coercion (§13); the presheaf one is the natural one for descriptions.

**Coherence.** A coherence theorem says that the reduction space has
contractible components: behaviours are bare sets of values, and evaluation
is path-independent.

> **A4** [LEAN][beh_equiv_type_of_terminal]. If every reduction is a step and
> `A` has a terminal object, behaviours are equivalent to sets.

A terminal object is a normal form that everything reduces to, uniquely. The
proof is short and structural: the functor from `A` to the point has a fully
faithful adjoint picking out the terminal object, so it is a localization at
all maps [LEAN][localization_trivial_of_terminal].

### 9. Example: associativity and the pentagon

One binary operation, one oriented rule `α : (x y) z → x (y z)`, and no
equations between reductions beyond interchange.

On four letters there are five bracketings and five rule instances, forming a
pentagon. Nothing forces it to commute, because the two redexes of
`((x y) z) w` overlap and interchange does not apply. So the reduction
category is the free category on the pentagon graph, and there are two routes
from `((xy)z)w` to `x(y(zw))`: `top` with two steps and `bot` with three.

> **P2** [LEAN][top_ne_bot_localized]. `top` and `bot` remain distinct after
> inverting every reduction.
>
> [LEAN][exists_beh_top_ne_bot]. There is a behaviour on which they act
> differently.

The witness is a weight: send every bracketing to ℤ and let a reduction add
the number of times it uses the edge `((xy)z)w → (xy)(zw)` [LEAN][wt_top_ne_wt_bot].
`top` uses it once and `bot` never, so on this behaviour, evaluating
`((xy)z)w` remembers which way one reduced.

By hand, more is true [HAND]: the classifying space of the free pentagon is a
circle, behaviours over it are sets with an automorphism, and evaluating
`((xy)z)w` gives a ℤ-torsor, not a point. Lean checks the shadow of this that
the theory needs: the loop is nontrivial and ℤ detects it.

**Imposing the pentagon.** If `top = bot` is imposed, the hom-categories
become the Tamari order, which has a top element, the right-bracketed form
([MEMORY] Laplaza 1972 proved coherence for non-invertible associativity with
the pentagon). Over the four-variable Tamari order, A4 applies and behaviours
are bare sets [LEAN][tamari_beh_bare]. That the quotient of the free pentagon
by `top = bot` *is* that order is stated in Lean but not yet proved.

**The pattern.** Overlapping rules make holes; imposing the coherence that
fills them is a choice, and leaving it free gives a completely regular tower
of cells, one per arity ([MEMORY] Stasheff; Guiraud and Malbos for the
general control principle).

### 10. Example: SKI, the cocycle, and two kinds of divergence

**Setup.** Constants `S`, `K`, `I`, binary application, and the rules

    I x      →  x
    K x y    →  x
    S x y z  →  x z (y z)

Steps are data: `I (I x)` reduces to `I x` in two different ways, by the
outer redex or the inner one [LEAN][accident_SKI]. This is the same accident
as in §7, now in syntax.

**Permutation equivalence.** Two reductions are equivalent when they differ
by elementary squares: disjoint redexes commute, and each rule is natural in
each argument, closed under contexts and composition [LEAN][Sq]. That this
is Lévy's permutation equivalence is [MEMORY]; it matters only for the
interpretation.

**The loop at Ω.** Let `Ω = S I I (S I I)`. Then

    S I I (S I I)
      →  I (S I I) (I (S I I))      S-step at the root
      →  S I I (I (S I I))          I-step in function position
      →  S I I (S I I)              I-step in argument position

is a non-identity endomorphism of `Ω`.

**The cocycle.** Count the S-steps whose redex lies on the right spine, the
positions reached by argument moves only [LEAN][Step.wt]. This is the functor
to the one-object groupoid on ℤ that interprets application by `(g, h) ↦ h`,
the S-rule by 1 and the I-rule by 0.

> **K6** [LEAN][wt_permEq]. On K-free terms, the weight is invariant under
> permutation equivalence.

The proof checks each elementary square [LEAN][sq_wt]. The interesting one is
naturality of S in its third argument `z`, which S duplicates. A step `c`
inside `z` is counted once on each side: before the S-step it sits on the
spine; after it, one copy lands in `x z` (off the spine, weight 0) and one in
`y z` (on the spine). The K-free hypothesis is needed only to rule out the
two naturality squares of K. The one for K's erased argument says that a
step inside the discarded argument, followed by the K-step, equals the K-step
alone; the left side can carry weight and the right side cannot. So with K
the only such model is trivial [HAND].

**Two kinds of divergence.**

> **K7** [LEAN][not_absorbed]. The loop at `Ω` has weight 1
> [LEAN][omegaLoop_wt], so no reduction out of `Ω` absorbs it: there is no `h`
> with `h ∘ e` equivalent to `h`.
>
> **K8** [LEAN][absorbed]. In `K a Ω`, the K-step absorbs the loop:
> `κ ∘ e′` is equivalent to `κ`.

So divergence comes in two kinds, and only the directed structure tells them
apart. In `K a Ω` the divergence is avoidable: there is a way out that makes
the loop irrelevant. At `Ω` it is unavoidable. With a calculus of fractions,
"some continuation absorbs `e`" is exactly "`e` dies in π₁" ([HAND],
standard), so K7 says the loop survives as monodromy. Lean proves the
absorption statement; the step to π₁, and that the loop has infinite order
there, are [HAND]. That the loop also survives in full SKI is [HAND], given
the standard residual theory [CITED].

**Three readings of a loop** [HAND]. The map `End(t) → π₁` separates three
cases: the pentagon is a loop not coming from any endomorphism (a coherence
defect, harmless to fill); the loop in `K a Ω` is an endomorphism that dies
(avoidable divergence); the loop at `Ω` is an endomorphism that survives
(unavoidable divergence). Filling the pentagon is harmless; filling a
directed cycle would say that looping is doing nothing.

### 11. Example: groups and the Dehn function

**Setup.** A group presentation `⟨X | R⟩`. Descriptions are elements of the
free group on `X`. A step deletes a relator or its inverse from anywhere:
`u r v → u v`, at cost 1. Free reduction costs nothing because descriptions
are free-group elements.

> **G3** [LEAN][dchain_iff_prodConj]. `n` deletions take `w` to `1` exactly
> when `w` is a product of `n` conjugates of relators and their inverses.
> Hence minimal trace cost equals area [LEAN][cost_eq_area].

The key identity is `u r v = (u r u⁻¹)(u v)`: each deletion peels off one
conjugate, and a product of conjugates is deleted one conjugate at a time.
So the Dehn function is the complexity function of the presentation. Every
step here is reversible (deleting `r` undoes deleting `r⁻¹`): groups are the
undirected case, which is why the Dehn function is a filling invariant.
([MEMORY] Sapir, Birget and Rips: Dehn functions of finitely presented groups
track the nondeterministic time complexity of the word problem.)

This example is also what showed that cost cannot be added by enriching in
`[0,∞]`, whose underlying maps are only the cost-0 ones; the right base is
normed sets [HAND, MEMORY].

### 12. Theorem B: morphisms

**Simulations.** A simulation between presentations is an adjunction
`G ⊣ R` between their categories of descriptions whose left adjoint sends
steps to computations [LEAN][Simulation]. (The notes define a simulation as a
cocontinuous functor between presheaf categories; such a functor has a right
adjoint, so here the adjunction is taken as part of the data.)

> **B1** [LEAN][isLocal_of_adj]. If `G` sends steps to *conversions*, then `R`
> sends behaviours to behaviours.

Only conversions are needed: precomposition with a step on `Hom(–, R Z)`
transposes to precomposition with `G s` on `Hom(–, Z)`, a bijection because
`Z` is a behaviour and `G s` a conversion.

> **Theorem B** [LEAN][adjOnBeh]. A simulation induces an adjunction between
> behaviour categories: `L′ ∘ G` on behaviours is left adjoint to `R`
> restricted to behaviours.

Here the size condition shows up again, and for the same reason: `L′`, the
evaluation of the target presentation, has to exist. Consequences, all
[LEAN]:

- **Saturation.** `G` sends all computations to computations, not just steps,
  and `R` preserves `M` [LEAN][G_preserves_E].
- **Composition.** Simulations compose [LEAN][Simulation.comp].
- **Completion is harmless.** Adding rules that are already conversions does
  not change the behaviours [LEAN][isLocal_eq_of_le_of_le_conv], and adding
  rules already in `E` does not change `E` either [LEAN][E_eq_of_le_of_le_E].
  This is why Knuth–Bendix completion is harmless.
- **Uniting rule sets** intersects behaviours [LEAN][isLocal_sup].

**Translations and the double category** [HAND]. A translation is a functor
`F : A → A′` on terms whose pushforward (left Kan extension) sends steps to
computations; it is a representable simulation, and compilers are
translations when the encoding is functional. Translations are tight and
simulations loose, and presentations form a double category. A translation
has a conjoint exactly when restriction along it also preserves computations,
a step-lifting condition that coverings satisfy; then restriction on
behaviours has adjoints on both sides. The double category fails to be an
equipment exactly where simulation differs from bisimulation. Translations
and the conjoint statement are stated in Lean but not proved; the double
category itself is not formalized.

### 13. Coercion

A **type family** is a map `p : Y → X` in `M`. For a computation `e` and a
type family `p`, every square has a unique filler:

$$
\begin{array}{ccc}
T & \xrightarrow{\;\;y\;\;} & Y \\
{\scriptstyle e}\Big\downarrow & \nearrow{\scriptstyle \exists!\,d} & \Big\downarrow{\scriptstyle p} \\
T' & \xrightarrow{\;\;x'\;\;} & X
\end{array}
\qquad \operatorname{coe}_e(y) := d
$$

**Coercion inverts restriction.** Restriction along `e` (substitution) always
exists. Orthogonality of `e` and `p` is exactly the statement that it is a
bijection on every fibre [LEAN][orth_iff_restrict_bijective], and coercion is
its inverse [LEAN][coerce]. Strict functoriality follows:
`coe` along `e′ ∘ e` is `coe` along `e`, then along `e′`
[LEAN][coerce_comp]. Coercion is a property of the family, not chosen
structure, and coercing around a loop of computations is an automorphism of
the fibre: this is where types feel holes.

**The type formers are closure properties of `M`** [LEAN]:

- substitution: `M` is stable under pullback [LEAN][rOrth_of_isPullback];
- pairs: `M` is closed under composition [LEAN][rOrth_comp];
- equality: the diagonal of an `M`-map is in `M` [LEAN][rOrth_diagonal];
- adjunctions transpose lifting problems [LEAN][orth_adj], which is how the
  function case reduces to a pulled-back square.

**What it takes for dependent types** [HAND]. Function types of type families
are type families when computations are stable under pullback along
`M`-maps, a Frobenius condition ([MEMORY] the same shape as Gambino and
Sattler's). The universe of behaviours is itself a behaviour when `L` is left
exact; for covariant families, confluence makes the colimit computing `L`
filtered, and filtered colimits commute with finite limits. So confluence is
what lets types themselves be coerced along computation.

### 14. The knobs

The definition has parameters, kept brief here [SPEC for the assembly,
individual coordinates as labelled in the notes].

- **Enrichment: what a probe returns.** Truth values give reachability
  preorders, costs give directed metric spaces, sets give categories of
  reductions, spaces give holes. Change of base from graphs to categories to
  posets to sets takes small-step to big-step to denotational semantics
  ([CITED] Baez and Williams); the dynamic picture adds a rung for spaces,
  where Squier-type invariants live [HAND].
- **Probe shapes.** A choice of path shapes in time, which is where
  bisimulation and open maps come in.
- **Arities.** Which probes are small. Some smallness constraint must survive,
  because it is what makes evaluation exist (§7) [HAND].
- **Self-classification.** Whether the presentation can describe its own
  rewriting; this is where universality, and the Church–Turing robustness,
  come from.

### 15. Open problems and what comes next

**What the formalization changed.** Four statements in the notes were
corrected while making them precise; each is recorded in the changelog.

1. *Variance.* The proof map stated Theorem A for covariant families, where
   steps run from contractum to redex. It is now stated for presheaves, with
   the covariant version proved alongside.
2. *Convergence.* "Conversions are the 2-out-of-3 closure of `E`" holds under
   convergence; "convergence is equivalent to the existence of `L`" is only
   one direction.
3. *Groupoid.* The two variances agree on behaviours when the steps generate
   `A`, not unconditionally.
4. *The collapse lemma* is stronger than stated: a characterization, robust
   to the side of the adjoint and to invertible units.

**Not yet proved in Lean** (stated, tier "stretch"): traces as pushouts of
steps; translations via left Kan extension and conjoints; that the free
pentagon modulo `top = bot` is the Tamari order; the reduction category of
SKI and the infinite order of the loop in it.

**Open problems.**

1. **The lax theory.** Factorization systems one directed level up, so that
   coherences between reductions can themselves be directed. Any
   factorization system is a degenerate pairing of a coalgebra and an algebra
   (computations are coalgebras for a comonad, type families algebras for a
   monad); in an orthogonal system both are idempotent and the pairing is
   invisible. It becomes real structure exactly here [SPEC].
2. **Convergence and the reflector.** Does a reflector onto behaviours give a
   factorization of every map? This needs reflection in every slice.
3. **Higher coherence** of the reduction space beyond level 1.
4. **Ω in full SKI** without assuming the residual theory.
5. **Abstract interpretation** as the adjunction of Theorem B [SPEC].
6. **A finer directed invariant** than `End(t) → π₁`.

**For a second post.** Type theories as presentations whose rules are units
and counits of local adjunctions, and what polarity predicts about η; the two
fibres of dependent type theory; the arena where higher coherence calms down;
tree calculus and a tight and loose reading of Church–Turing.

---

*Lean links point to commit `a699a1d` of the repository. The axiom audit for
every linked declaration is in `AXIOMS.md`; the changes made to the original
statements are in `PROOF_CHANGELOG.md`.*

[steps_le_E]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L48
[E_le_Conv]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L52
[beh_iff_M]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L57
[isRightAdjoint_of_convergent]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L87
[conv_le_of_E_le]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L102
[unit_mem_Conv]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L134
[conv_iff_isIso_L]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L129
[toPresentation]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Presentation.lean#L153
[rOrth_terminal_iff_isLocal]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L288
[orth_iff_restrict_bijective]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L174
[coerce]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L219
[coerce_comp]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L251
[rOrth_of_isPullback]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L78
[rOrth_comp]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L72
[rOrth_diagonal]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L110
[orth_adj]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Orth.lean#L132
[beh_iff_map_bijective]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L147
[behEquivInverting]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L172
[behEquivLocalSystems]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L182
[localization_trivial_of_terminal]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L188
[beh_equiv_type_of_terminal]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L194
[behEquivLocalSystemsCo]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/LocalSystems.lean#L248
[isLocal_of_adj]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L26
[isLocal_sup]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L42
[isLocal_eq_of_le_of_le_conv]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L54
[E_eq_of_le_of_le_E]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L64
[Simulation]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L78
[adjOnBeh]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L96
[G_preserves_E]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L110
[Simulation.comp]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Translation.lean#L123
[collapse]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L93
[collapse_of_isIso_unit]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L77
[collapse_of_isIso_counit]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L102
[lax_orthogonal_iff]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L135
[forget_isEquivalence_of_unique]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L142
[accident]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L174
[not_lax_orthogonal]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Collapse.lean#L179
[wt_top_ne_wt_bot]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Pentagon.lean#L66
[top_ne_bot_localized]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Pentagon.lean#L74
[exists_beh_top_ne_bot]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Pentagon.lean#L99
[tamari_beh_bare]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Pentagon.lean#L152
[dchain_iff_prodConj]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Dehn.lean#L73
[cost_eq_area]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/Dehn.lean#L82
[accident_SKI]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/Syntax.lean#L53
[Step.wt]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/Weight.lean#L17
[omegaLoop_wt]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/Weight.lean#L62
[Sq]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/PermEq.lean#L18
[sq_wt]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/PermEq.lean#L59
[wt_permEq]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/PermEq.lean#L79
[not_absorbed]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/PermEq.lean#L90
[absorbed]: https://github.com/maxinelevesque/formal-computation/blob/a699a1d0ed4f63c11f05a98c656f818a4993d2e8/FormalComputation/SKI/PermEq.lean#L97
