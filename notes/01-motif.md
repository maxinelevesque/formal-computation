# 1. The motif

## 1.1 The question

In computer science "computation" is often treated as self-evident and close
to ontologically primitive. The aim here is a natively relational account:
one where categorical and double-categorical structure is primary, strict and
set-like things are derived, and the form of computation is visible without
backing down to sets. There is something real in the usual intuition, "the
complexity of constructing a solution from predefined structural primitives".
The goal is to say what that is, structurally.

## 1.2 The slogan

**Computation is composition with its bookkeeping left in.**

In a category, `g ∘ f` simply is. Anything given by a universal property or a
presentation is given only implicitly. One thing has many descriptions, and
composing two descriptions yields a formal juxtaposition, not an answer.

So descriptions form a space fibred over the things they describe.

- **Denotation** is π₀ of that space.
- **Computation** is the directed geometry of the fibres, which π₀ forgets.

Three things fall out.

- **Where the moves come from.** Every basic step is a constructor meeting its
  destructor: an introduction followed by an elimination, a zigzag of unit and
  counit. Computation is the triangle identity held as a directed 2-cell
  instead of an equation, like pulling a kink straight in a string diagram.
  β-reduction, cut elimination and trace-style execution are that one gesture.
  [MEMORY] Seely 1987 treats λ-calculus as a 2-category with β and η as counit
  and unit of a lax adjunction.
- **What a value is.** A normal form is a terminal object in its fibre: the
  description that wears its identity on its face. Termination and confluence
  say every fibre has one and you cannot miss it. The discrete, set-like
  things are the skeleton of the fibres, not the ground beneath them.
- **What complexity is.** Running cost is distance travelled in a fibre. The
  difficulty of constructing a solution is the size of the cheapest cell
  filling a given boundary, an isoperimetric problem. [MEMORY] This is literal
  for groups: Sapir, Birget and Rips showed Dehn functions of finitely
  presented groups track nondeterministic time complexity of the word problem.

The usual CS picture reads this from the other end. It takes the input-output
function as the thing and computation as its implementation. Here the function
is the shadow and the fibre is the thing. The sense that the Turing notion is
privileged comes from robustness: any presentation rich enough to describe its
own rewriting sees the same fibre geometry up to simulation.

## 1.3 Other portraits of the same motif

Each of these was an "anchor" early in the conversation. All [MEMORY] unless
linked in `10-prior-art.md`.

- **Rewriting as 2-cells.** Orient the equations of a theory instead of
  imposing them. A cartesian closed category is what is left after collapsing
  β and η to equations.
- **Primitives as a computad.** "Construction from predefined structural
  primitives" is a cell in the free n-category on a polygraph (Burroni). Its
  complexity is its size in generating cells. Bonfante and Guiraud characterize
  polynomial time this way.
- **Cohomology of computation.** Squier: a monoid with a finite convergent
  presentation satisfies homological finiteness conditions. Whether a theory
  can be computed by rewriting at all is obstructed by invariants of the
  presented object. Guiraud and Malbos push this to higher dimensions.
- **Double categories.** The tile model of Gadducci and Montanari: horizontal
  cells are configurations, vertical cells are observations, squares are
  rewrites that compose both ways.
- **Normalization as gluing.** In dependent type theory, computation is the
  strict part: definitional equality. Normalization is a coherence theorem.
  The modern proofs go by Artin gluing (Altenkirch–Hofmann–Streicher, Fiore,
  Coquand, Sterling's synthetic Tait computability).
- **Computability without sets.** Cockett and Hofstra's Turing categories.

## 1.4 The gauge analogy

A physicist's reading of gauge theory: our descriptive apparatus is too floppy
for the thing described, so the description has redundant structure, and one
studies the fibres of the description in order to quotient them out. The gauge
field is, on this reading, an artefact of the irreducible wrongness of the
available descriptions.

The same shape applies here. There is an underlying thing (for type theory,
richly specified behaviour) and a floppy language for it. Computation is the
fibre structure of the language over the thing.

**Sharpening** [CITED for the polygraph facts]. The modern form is resolve,
do not quotient, as in BRST. A presentation with its rewrites, and rewrites
between rewrites, is a cofibrant resolution of the real thing. Polygraphs are
exactly the cofibrant objects in the folk model structure on strict
ω-categories. Rewrites play the role of ghosts; critical pairs are
ghosts-for-ghosts. Any two resolutions are equivalent, so the undirected
moduli is contractible, which is why the holes belong to the thing and not
the description.

**Where the analogy breaks.**

- The fibres are directed. They are not torsors. The orientation is extra data
  that is not contractible.
- Cost is not pure gauge. It behaves like holonomy: the Dehn function survives
  change of presentation up to coarse equivalence. Complexity is the real
  residue of the "unreal" fibre.
- Later finding (`06` §6.2): loops in a fibre come in kinds, and only the
  directed structure can tell them apart.
- Later finding (`01` §1.5): the base is not prior to the fibre.

## 1.5 Tame and wild fibres; why Turing

Turing computation is not one fibre shape among others. It is the universality
class you fall into once fibres stop being tame.

- **Tame.** Every fibre has a terminal object. Type theories live here, graded
  by how tall fibres get, which is what proof-theoretic ordinals measure
  ([MEMORY] ε₀ for System T).
- **Wild.** Some fibres have no terminal object, and it is undecidable which.

The tame stratum has no top: a diagonal argument stops any total language from
being universal for total computation. Add unrestricted fixpoints and
everything collapses to one class up to simulation. [SPEC] Turing computation
is the boundary at infinity of the tame moduli.

[MEMORY] Higman's embedding theorem gives a machine-free statement: a finitely
generated group embeds in a finitely presented one exactly when it is
recursively presented. "Computable" means "lives inside something finitely
presented".

[MEMORY] The collapse to a single class happens only for functions ℕ → ℕ. At
higher types there are inequivalent natural notions of computability (Longley
and Normann), organized by partial combinatory algebras and applicative
morphisms, each with its own realizability topos.

## 1.6 What a type is

**The bundle is "finite doings over what they mean", and a type is a
behaviour: a class of doings closed under every test you can run on them.**

- **Domain of discourse.** One universe of doings that can be plugged into
  each other and run, plus one primitive observation such as "it halted".
  That is essentially a partial combinatory algebra.
- **A type.** The relation "this doing passes this test" induces a Galois
  connection between sets of doings and sets of tests. A type is a closed set.
  With equality included, it is a partial equivalence relation: which doings
  count, and when two count as the same. A type is a contract on interaction,
  not a container of elements. This is Isbell duality in spirit.
- **Consequence for the gauge picture.** The base is not prior to the fibre.
  The "real thing" is constituted as the invariant of its descriptions.
- **Resolution and realizability** are the same bundle read in opposite
  directions. Realizability goes bottom-up, carving types out of raw doings.
  Resolution goes top-down: take the thing and free it, so every "is" becomes
  a "because", recorded as a cell. Gluing is the statement that they meet: a
  type is a relation between its syntax and its realizers.

This is one school's reading (Brouwer, Martin-Löf, Girard, Krivine). A
denotational semanticist would put the base first.

## 1.7 Where finiteness comes from

The first version of §1.6 took two properties of fibres as primary: finite
generation and reflexivity. That was rejected as reductive, and rightly: the
base was defined by probing while the fibre was defined by construction from
atoms. Both properties are shadows of structural parameters.

**Finiteness without cardinality.** Counting is the decategorified shadow of
at least three structural ideas.

- **Finite as dualizable.** In a monoidal category an object is "finite" when
  it has a dual, with unit and counit satisfying the zigzag identities.
  Finite-dimensional vector spaces are exactly the dualizable ones. Finite
  means "can be completely interacted with". This is the same zigzag as §1.2.
- **Finite as exhaustible.** Compactness says a universal check over the whole
  thing is itself a single observation. [MEMORY] Escardó: Cantor space admits
  exhaustive search in this sense though it is uncountable. Turing's 1936
  argument has this shape: symbols from a continuum blur together, so only
  finitely many are distinguishable at any resolution.
- **Small as classified.** Size is a relation to a universe: a map is small
  when it is pulled back from the universal one. [MEMORY] Joyal and Moerdijk's
  algebraic set theory axiomatizes a class of small maps with no cardinals.

Two further points.

- **Numbers as iteration.** The natural numbers object is the free thing on a
  point and an endomap: the shape of iteration. Outside Set, "finite" splits
  into several inequivalent notions, which suggests it was never one thing.
- **What cardinality becomes.** Trace of an identity, Euler characteristic,
  Leinster's magnitude of enriched categories.

**Pushback that stands.** The paradoxes are not the fault of sets. Lawvere's
fixed-point theorem runs the diagonal argument in any cartesian closed
category, and Girard's paradox hits type theory once a universe contains
itself. Membership-based set theory can be dropped, but size follows, because
it is the obstruction to a bundle classifying itself.

**Later sharpenings.**

- Size as existence of a reflector: `03` §3.6. This is the form that was found
  acceptable: a size condition that falls out as equivalent to something
  structural.
- Approximation derived from confluence: `06` §6.5.
- "Finite as dualizable" is the minimal setting of the arities knob: `02` §2.3.

**Reflexivity** is treated in `02` §2.4.
