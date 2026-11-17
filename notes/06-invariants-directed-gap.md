# 6. Invariants and the directed gap

## 6.1 The collapse lemma

**Question.** Can direction be kept by asking for *lax* orthogonality to each
rule?

**Setup.** Work in Cat. A model is a category `X` with functors
`l, r : Xⁿ → X` interpreting the two sides of a rule. "Freely add a 2-cell
`l ⇒ r`" is the co-inserter. Maps out of it into `X` form the **inserter**
category `Ins(l, r)`:

- objects: pairs `(a, φ)` with `φ : l(a) → r(a)`;
- morphisms `(a, φ) → (a′, φ′)`: maps `u : a → a′` with
  `r(u) ∘ φ = φ′ ∘ l(u)`.

There is a forgetful functor `U : Ins(l, r) → Xⁿ`.

Lax orthogonality (in the sense of Clementino and López Franco: left Kan
extensions along the co-inserter map exist and are honest extensions) says
`U` has a left adjoint section `σ : a ↦ (a, ρₐ)` with identity unit.

> **Lemma** [HAND]. If `U` has a left adjoint section with identity unit, then
> for every `a` there is exactly one arrow `l(a) → r(a)`, namely `ρₐ`.

*Proof.* The adjunction bijection `Ins(σ a, (a′, φ′)) ≅ Xⁿ(a, a′)` is given by
`U`. So every `u : a → a′` is a morphism `(a, ρₐ) → (a′, φ′)`, for every `φ′`.
Take `u = id`: then `ρₐ = φ′` for every `φ′ : l(a) → r(a)`. ∎

The same argument works with a right adjoint section, and with pseudo instead
of strict orthogonality.

**Counterexample** [HAND]. The I-rule gives a copointed endofunctor `(I, ι)`.
In the free one, `ι_{I a}` and `I(ι_a)` are distinct: they are the two
reductions of `I (I a)`. A concrete model where they differ: on types, take
`I = (– × Bool)` and `ι` the first projection. Then `ι_{I a}` drops the outer
Boolean and `I(ι_a)` drops the inner one.

**Conclusion.** Rule cells are structure, not property. The monad that adds
them is not lax idempotent. Direction must be carried by the factorization
system (`03` §3.2).

**Refinement** (`07` §7.1). Rules that are units or counits of local
adjunctions are property-like without collapsing: there can be many 2-cells
from redex to contractum, but the rule is canonically the universal one.

## 6.2 Loops: a trichotomy

`C` alone cannot tell a fillable loop from a divergence. The functor `L` can.

**The invariant** [HAND]. `L` restricted to endomorphisms:

    End(t)  →  π₁(reduction space, t)

It needs no new machinery.

| | `End(t)` | Image in π₁ | Reading |
|---|---|---|---|
| Pentagon (`04` §4.2) | trivial | π₁ = ℤ, not from endomorphisms | **Coherence defect**: a zigzag loop; fillable |
| `K a Ω` (`04` §4.1) | nontrivial | trivial | **Avoidable divergence**: weakly normalizing |
| Bare directed cycle; `Ω` in K-free SKI | ℕ | embeds in ℤ | **Unavoidable divergence** |

Filling the pentagon is harmless. Filling a directed cycle would say that
looping is doing nothing.

**Correction recorded.** Earlier it was said that SKI's loop is "not a hole".
In the directed fibre it is an endomorphism; after localization it is
monodromy too.

## 6.3 Absorption

> **Criterion** [HAND, standard]. If the reduction category has a calculus of
> left fractions (completing squares plus cancellation), then a loop `e` at
> `t` dies in π₁ exactly when some reduction `h` out of `t` absorbs it:
> `h ∘ e = h`.

So a divergence is avoidable exactly when some continuation absorbs it. The
K-step in `K a Ω` does.

[CITED] Mathlib formalizes Gabriel–Zisman calculus of fractions.

## 6.4 Cocycles

**Models in groupoids detect π₁** [HAND]. A model of the 2-theory in a
groupoid sends every reduction to an isomorphism, so it gives a functor from
the reduction category to a groupoid, hence a representation of the reduction
groupoid. A model in a one-object groupoid on an abelian group `G` gives a
class in `H¹` of the reduction space with coefficients in `G`.

The right-spine S-count of `04` §4.1 is such a class.

**Strategy-independent lower bounds** [HAND]. A non-negative additive weight
on steps that respects the equations between reductions is both a cost and a
1-cocycle. On a coherent fibre it is path-independent. If it is bounded above
by step cost, it bounds every evaluation strategy from below.

**A loop with positive invariant cost is unavoidable** [HAND]: if
`W(e) > 0` then `W(h ∘ e) ≠ W(h)` for every `h`, so nothing absorbs `e`.

## 6.5 Approximation, derived

Here descriptions are representable **presheaves**: `y(t) = A(–, t)`, which is
covariant in `t`. (Type families are covariant functors; see `03` §3.4 for how
the two variances coexist.)

> **Claim** [HAND]. With a calculus of left fractions, the reducts of `t` form
> a filtered category and
> `L y(t) = colim over reducts t → t′ of y(t′)`.
> Pointwise: `(L y(t))(u) = colim over t → t′ of A(u, t′)`, the fractions
> from `u` to `t`.

So **the value of a term is the ind-object of its reducts.** This is Scott's
"limit of finite approximations", obtained from confluence and not assumed.

> **Claim** [HAND]. In a convergent, coherent system, `t` has a normal form
> exactly when that ind-object is representable.

Two-sided check: if `n` is terminal in its component then `y(n)` is local
(every reduction into `n` factors uniquely through any step) and
`L y(t) ≅ y(n)`.

With cost, the filtered diagram carries a rate of convergence.

## 6.6 What remains of the directed gap

- [OPEN] The lax theory. If coherences between reductions should themselves be
  directed (standardization as rewriting on reductions), one needs lax
  factorization systems one directed level up. [CITED] Clementino and López
  Franco's lax orthogonal factorization systems are the nearest existing tool;
  [CITED] a 2025 thesis identifies orthogonal factorization systems with a
  class of double categories.
- [OPEN] Whether `Ω`'s loop survives in full SKI without assuming residual
  theory.
- [SPEC] Directed topology (natural homology) as a finer invariant than
  `End(t) → π₁`.
