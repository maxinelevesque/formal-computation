# 8. Coercion

All [HAND] unless marked. Diagrams use `$$ … $$` math with arrays, which
GitHub renders.

## 8.1 Coercion is the unique filler

- A **family** is any map $p : Y \to X$ in $P$.
- A **type family** is a family in $M$.
- For a computation $e \in E$ and a type family $p \in M$:

$$
\begin{array}{ccc}
T & \xrightarrow{\;\;y\;\;} & Y \\
{\scriptstyle e}\Big\downarrow & \nearrow{\scriptstyle \exists!\,d} & \Big\downarrow{\scriptstyle p} \\
T' & \xrightarrow{\;\;x'\;\;} & X
\end{array}
\qquad \operatorname{coe}_e(y) := d
$$

For all squares at once, the comparison map is an isomorphism:

$$
P(T',Y) \;\xrightarrow{\;\cong\;}\; P(T,Y)\times_{P(T,X)} P(T',X)
$$

## 8.2 Coercion inverts restriction

Write $Y_{x'} = \{\, d : T' \to Y \mid p\,d = x' \,\}$ for the fibre over a
point $x'$. Restriction along $e$ always exists (it is substitution), and
$p \in M$ says it is a bijection:

$$
e^* : Y_{x'} \xrightarrow{\;\cong\;} Y_{x'e}, \qquad \operatorname{coe}_e = (e^*)^{-1}
$$

Strict functoriality follows from $(e'e)^* = e^*e'^*$:

$$
\operatorname{coe}_{e'e} = \operatorname{coe}_{e'}\circ\operatorname{coe}_{e}, \qquad \operatorname{coe}_{\mathrm{id}} = \mathrm{id}
$$

What comes for free:

- **Strictness.** Coercion is a property of the family, not chosen structure.
- **Completion.** Any family factors as a computation followed by a type
  family: the free family with coercion.
- **Monodromy.** Coercing around a loop of computations is an automorphism of
  the fibre. This is where types feel holes.

## 8.3 Substitution

$M$ is stable under pullback. Paste the lifting problem onto the pullback
square and solve against $p$; the pullback property gives the unique lift.

$$
\begin{array}{ccccc}
T & \longrightarrow & \sigma^*Y & \longrightarrow & Y \\
{\scriptstyle e}\Big\downarrow & & \Big\downarrow & & \Big\downarrow{\scriptstyle p} \\
T' & \longrightarrow & X' & \xrightarrow{\;\sigma\;} & X
\end{array}
$$

So coercion in a constant family is the identity.

## 8.4 Pairs and equality

**Pairs.** $M$ is closed under composition. For $Z \xrightarrow{q} Y
\xrightarrow{p} X$ lift against $p$, then against $q$:

$$
\operatorname{coe}^{\Sigma}_e(a,b) = \big(\operatorname{coe}^{A}_e a,\; \operatorname{coe}^{B}_e b\big)
$$

**Equality.** The diagonal of an $M$-map is in $M$, by cancellation:

$$
Y \xrightarrow{\;\Delta\;} Y\times_X Y \xrightarrow{\;\pi_1\;} Y, \qquad
\pi_1\Delta = \mathrm{id} \in M,\;\; \pi_1 \in M \;\Rightarrow\; \Delta \in M
$$

## 8.5 Functions: the Frobenius condition

The adjunction $p^* \dashv \Pi_p$ transposes lifting problems:

$$
\begin{array}{ccc}
T & \longrightarrow & \Pi_p Z \\
{\scriptstyle e}\Big\downarrow & \nearrow & \Big\downarrow \\
T' & \longrightarrow & X
\end{array}
\quad\Longleftrightarrow\quad
\begin{array}{ccc}
p^*T & \longrightarrow & Z \\
{\scriptstyle p^*e}\Big\downarrow & \nearrow & \Big\downarrow{\scriptstyle q} \\
p^*T' & \longrightarrow & Y
\end{array}
$$

The right-hand square has a unique filler when $p^*e \in E$. So function types
of type families are type families when **$E$ is stable under pullback along
$M$-maps**. Unwinding the transpose:

$$
\operatorname{coe}^{\Pi}_e(f)(a') = \operatorname{coe}^{B}_e\!\big(f(\operatorname{coe}^{A\,-1}_e a')\big)
$$

In the dynamic picture Frobenius holds: a step pulled back along a covering is
a disjoint union of lifted steps.

[MEMORY] This is the same shape as Gambino and Sattler's Frobenius condition
for uniform fibrations.

## 8.6 The universe: exactness of L

The universe of behaviours is itself a behaviour when $L$ is left exact.
[MEMORY] Rijke, Shulman and Spitters, for lex modalities.

For **covariant** families, a calculus of fractions gives

$$
(LB)(t) = \operatorname*{colim}_{t \to t'} B(t')
$$

Confluence completes every span of reducts, which makes the indexing category
filtered, and filtered colimits commute with finite limits:

$$
\begin{array}{ccc}
t & \longrightarrow & t' \\
\Big\downarrow & & \Big\downarrow \\
t'' & \longrightarrow & t'''
\end{array}
$$

So **confluence is what lets types themselves be coerced along computation.**

Variance check, to be redone carefully. For contravariant families the
indexing category runs over common ancestors, and a small counterexample shows
exactness can fail: on the cospan $a_1 \to c \leftarrow a_2$, $L$ is a pushout
of sets, which does not preserve products.

## 8.7 The two fibres

The weak factorization system $(\mathcal{L}_w, \mathcal{R}_w)$ of
identifications uses the same square with $\exists$ in place of $\exists!$.

| | Computations | Identifications |
|---|---|---|
| Factorization system | orthogonal | weak |
| Coercion | unique filler | chosen filler |
| Status | property | structure |
| Functoriality | strict | up to homotopy |

Compatibility:

$$
E \subseteq \mathcal{L}_w, \qquad \mathcal{R}_w \subseteq M
$$

and for $e \in E$, $p \in \mathcal{R}_w$ the chosen filler is the unique one.
That is the precise form of "coercion along $\rho$ is transport along its
companion". Cubical Kan operations are one way to discharge the coherence
obligation on the weak side.

## 8.8 Summary

Coercion rules by type former are closure lemmas for $M$. Two conditions on a
presentation are needed before it supports dependent types: Frobenius, and
exactness of $L$. Confluence supplies the second.
