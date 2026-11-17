# 4. Examples

## 4.1 SKI

**Setup.** Constants `S`, `K`, `I` and binary application. Rules:

    I x      →  x
    K x y    →  x
    S x y z  →  x z (y z)

**No overlaps.** The three rules never overlap (an orthogonal system). Every
local divergence is between disjoint or nested redexes. In the cartesian
2-theory those squares are instances of interchange and naturality, so no new
3-cells are needed: SKI is coherent at the Cat level for free. [MEMORY] This is
Lévy's permutation equivalence, axiomatized by Laneve and Montanari; [CITED]
Hirschowitz does the higher-order case.

**So universality and higher coherence are independent axes.** SKI is fully
reflexive and has trivial coherence. Holes come from overlapping rules (§4.2).

**The syntactic accident.** `I (I x)` reduces to `I x` in two different ways,
by the outer redex or the inner one. They are distinct arrows. Their
composites down to `x` agree, by naturality of the I-rule. This example is the
counterexample in the collapse lemma (`06` §6.1).

**The loop at Ω.** Let `Ω = S I I (S I I)`. Then

    S I I (S I I)
      →  I (S I I) (I (S I I))      S-step at the root
      →  S I I (I (S I I))          I-step in the left (function) position
      →  S I I (S I I)              I-step in the right (argument) position

This is a non-identity endomorphism `e` of `Ω` in the reduction category. The
two orders of the I-steps are equal by interchange.

**The cocycle** [HAND]. Take the one-object groupoid on ℤ. Interpret
application on arrows by `(g, h) ↦ h`, the S-rule by 1 and the I-rule by 0.

- Both sides of the I-rule are the identity functor, and both sides of the
  S-rule send `(f, g, h)` to `h`. So each rule is a natural transformation
  between equal functors, and any element of ℤ will do. This is a model of the
  K-free 2-theory.
- A step inside a function position is sent to 0; a step inside an argument
  position keeps its value. So the induced functor counts **S-steps whose
  redex lies on the right spine** (positions reached by argument moves only).
- On the loop: the root S-step counts 1, the left I-step counts 0, the right
  I-step counts 0 (it is an I-step). Total 1.

So the loop has infinite order in π₁ of the K-free reduction space.

Direct check of the hard square, an S-redex on the right spine with an inner
S-redex equal to its third argument `z`. Inner then outer: 1 + 1. Outer then
the two copies: 1, then the copy in `x z` (not on the spine, 0) and the copy
in `y z` (on the spine, 1). Both sides are 2.

**With K the model must be trivial.** Naturality of the K-rule forces the
argument weight to vanish and then the group to be trivial. That matches K's
ability to erase loops.

**Avoidable divergence.** In `K a Ω`, the loop inside `Ω` is a nontrivial
endomorphism `e′`. Naturality of the K-step `κ : K a Ω → a` in its second
argument gives `κ ∘ e′ = κ`. So the loop dies in π₁.

**Full SKI** [HAND, given CITED residual theory]. Assume the reduction
category matches Lévy's, so it has completing squares and cancellation, hence
a calculus of fractions. Then a loop `e` at `t` dies in π₁ exactly when some
reduction `h` out of `t` absorbs it: `h ∘ e = h`. Every reduct of `Ω` is
K-free, so `h` and `h ∘ e` lie in the K-free fragment, where the cocycle gives
`W(h ∘ e) = W(h) + 1`. Nothing absorbs `e`. The assumption is not checked.

See `06` for the general theory of loops.

## 4.2 Associativity

**Setup.** One binary operation and one rule `α : (x y) z → x (y z)`. Dynamic
picture, no equations between reductions imposed beyond interchange.

- **Three variables.** Two terms, one arrow. Contractible.
- **Four variables.** Five bracketings and five rule instances forming a
  pentagon. Nothing forces it to commute: the two redexes of `((x y) z) w`
  overlap, so interchange does not apply. The reduction category is the free
  category on the pentagon graph, and its classifying space is a circle.
- **Behaviours over the circle** are sets with an automorphism. Evaluating
  `((x y) z) w` gives a ℤ-torsor, not a point. The value remembers the winding
  number: which way you reduced.
- **Impose the pentagon.** The hom-categories become Tamari lattices. [MEMORY]
  Laplaza 1972 proved coherence for non-invertible associativity with the
  pentagon. Every component has a top element (the right-bracketed form), so
  it is contractible, `C` collapses to sets, and evaluation lands on the
  normal form.
- **Add the pentagon as a 3-cell instead.** At five variables the boundary of
  the next associahedron appears as an unfilled sphere. Continuing gives one
  cell per arity: Stasheff's A∞ pattern.

**The control principle** [MEMORY]. Guiraud and Malbos: for a convergent
presentation, the n-fold critical branchings generate the (n+1)-cells of a
polygraphic resolution. Higher cells are read off from overlaps, not chosen.
Squier's theorem is the first case.

**Čech analogy** [SPEC, made precise at level 1 in `05` §5.5]. Rules are a
cover, critical branchings are intersections, and the resolution is its Čech
complex. Anick's resolution is the precise algebraic version.

**Controlled coherence.** Imposing the pentagon as an equation calms
everything at the Cat level. Leaving it free gives an infinite but completely
regular tower.

## 4.3 Groups and the Dehn function

**Setup.** A group presentation `⟨X | R⟩`. Objects are elements of the free
group on `X`. A step replaces `u r v` by `u v` for `r` a relator or its
inverse, at cost 1. Free reduction and expansion cost nothing, since objects
are free-group elements.

**Claim** [HAND]. The minimal cost from `w` to the identity is `Area(w)`, the
least `N` such that `w` is a product of `N` conjugates of relators and their
inverses.

- At most `N`: free expansion rewrites `w` as such a product; delete the
  relators one at a time.
- At least `N`: `u r v = (u v)(v⁻¹ r v)`, so each deletion changes the element
  by one conjugate.

So the Dehn function is the complexity function of the presentation.

**Remarks.**

- Every step is reversible (deleting `r` undoes deleting `r⁻¹`). Groups are
  the undirected case, which is why the Dehn function is a filling invariant.
  The directed analogue for monoids is derivational complexity.
- This example is what showed `[0,∞]`-enrichment is the wrong base (`03` §3.5).

## 4.4 Simply typed λ-calculus

**Rules as local adjunctions** (`07` §7.1).

- Functions: "apply to a fresh variable" has λ as local right adjoint. Counit
  `β : (λx. b) a ⇒ b[a]`. Unit `η : f ⇒ λx. f x`, an expansion.
- Products: projecting has pairing as local right adjoint, same pattern.
- Unit type: every `t : 1` has a unique reduction to `⟨⟩`.

**Triangle laws.** `f a ⇒ (λx. f x) a ⇒ f a` is the identity, and
`λx. b ⇒ λy. (λx. b) y ⇒ λx. b` is the identity. They resolve the β/η critical
pairs, and they declare a would-be divergence to be trivial one dimension up.

**Hand checks** [HAND].

- Unit: any `r : t ⇒ ⟨⟩` equals the canonical one, by naturality and
  `η(⟨⟩) = id`.
- Nested redexes: for `(λx. (λy. y) x) a`, inner-first and outer-first agree
  by naturality of β in its body.
- The accident again: with `I = λx. x`, the two first steps of `I (I a)`
  differ, but their composites to `a` agree by naturality of β in its
  argument.
- η loops: `f ⇒ λx. f x ⇒ λx. (λy. f y) x ⇒ λx. f x` equals plain η.

**"Normal" means terminal.** A β-normal η-long form still has outgoing
reductions (expansions), but each has a β-retraction and the only endomorphism
is the identity. In this setting a normal form is a terminal object of its
component, not an object with no outgoing steps.

**Existing theorems.**

- [CITED] Hilken 1994: exactly this calculus of rewrites (β-reductions and
  η-expansions under 2-categorical equations), with the word problem for
  rewrites solved by canonical forms. Whether terminality is stated in those
  words was not checked.
- [CITED] Fiore and Saville: in the free cartesian closed bicategory there is
  at most one structural 2-cell between parallel 1-cells; one proof is by
  normalization-by-evaluation.
- [CITED] Hirschowitz: 2-cells of the free cartesian closed 2-category are
  proof terms up to permutation equivalence.

**Consequence.** On unit and simple function types there is no monodromy, and
the proof-irrelevant treatment of conversion loses nothing.

## 4.5 Natural numbers

Types: unit, functions, ℕ with zero, successor and a recursor. Rules: the two
β-rules of the recursor, as reductions. No η as a reduction.

- **Level-1 coherence** [HAND, expected]. The recursor's rules do not overlap
  with β or η for functions, and the squares checked close by naturality. No
  theorem was found to cite.
- **The fibres separate.** Define addition by recursion on the first argument.
  For a variable `x`, the terms `x + 0` and `x` are distinct normal forms, so
  no zigzag of computations connects them. Induction still gives a path.
- **What the path is.** At each numeral `n` it is the companion of the actual
  evaluation `n + 0 ⇒ n`. The identification is a family of computations
  indexed by the data, with no uniform computation behind it.
- **Sheaf reading** [CONJ]. The context `x : ℕ` is covered by its
  constructors, and induction glues along the cover. Conjecture:
  identifications are computations sheafified along constructor covers.
  Evidence: [CITED] Altenkirch, Dybjer, Hofmann and Scott needed a sheaf model
  over a Grothendieck topology on constrained contexts to decide equality with
  strong sums.
- **A gap in the design of `07` §7.6.** Canonicity fails as first designed: a
  closed number can get stuck on a coercion along a companion path, because
  the path eliminator computes only on reflexivity. Fix: coercion must compute
  by recursion on the type former, as in observational and cubical type
  theories (`08`).

## 4.6 Tree calculus

[CITED] Rules, in the "triage" form given on the tree calculus specification
page (one operator `△`, application left-associative):

    △ △ y z            →  y            (1)
    △ (△ x) y z        →  x z (y z)    (2)
    △ (△ w x) y △      →  w            (3a)
    △ (△ w x) y (△ u)  →  x u          (3b)
    △ (△ w x) y (△ u v) → y u v        (3c)

[MEMORY] Jay's original book uses three rules; the triage variant is credited
to Johannes Bader. Check which version the reader has in mind.

**Where it sits.** A first-order presentation without overlaps, like SKI.
Rules (1) and (2) are K and S. [CITED] Confluence follows from the rules not
overlapping and inspecting only values. So it is coherent at the Cat level for
free, and the trichotomy for loops applies unchanged.

**What is special.** Values are leaves, stems and forks: the initial algebra
of `X ↦ 1 + X + X²`. Application is the eliminator of that data type. So
programs are **positive** data, built and then inspected by cases, whereas
λ-calculus functions are **negative**, known only by how they respond.
"Code as data" means living on the built side of the polarity (`02` §2.2,
`07` §7.3).

**Why it is so controlled.** Tests can inspect code, so the closure of doings
under tests is discrete on values. Behaviours are syntax trees. There is no
extensional quotient, so no coherence problem can arise. The price is
abstraction: any change to the code is observable.

**Self-classification without encoding.** The classifier of programs is the
data type of values itself. The price is partiality.

**In the double category** (`05` §5.7). SKI maps into tree calculus by a
translation preserving application. The reverse exists only through encodings,
which is a simulation. [CITED] Jay and Vergara argue the Church–Turing thesis
conflates mutual simulation with equivalence; their evidence is definability
of program equality. That is the tight/loose distinction.

**On whether higher structure is needed.** Tree calculus sits at `V = Set`,
with a discrete closure and positive values. Nothing there needs higher
structure. The need starts when one reasons up to behaviour, for example
asking whether two tree programs compute the same function. Tree calculus
cannot decide that, and the question brings back the quotient, the sheaf
condition and the coherence. Both views are right, at different knob settings.

## 4.7 Shorter anchors

- **Sheaves.** `A` a site, `S` the covering sieves, `L` sheafification.
- **Lawvere theories.** `A` the free algebras on finite sets; structural steps
  force product preservation; rule steps impose the theory.
- **Realizability.** `A` partitioned assemblies, `Φ` exact completion.
- **Transition systems.** `A` a path category; deterministic systems are
  coverings.
