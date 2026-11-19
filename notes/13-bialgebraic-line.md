# 13. The bialgebraic line: what we have re-found, and where we generalize (working, 2026-11-19)

Status: research log being assembled into a synthesis. Each source is tagged:
- **[read]**: a research agent read the text this session;
- **[recalled]**: not re-checked this session;
- **[inferred]**: our argument.

DOIs were checked against Crossref or DataCite unless marked otherwise.

## 13.0 Synthesis

### The picture Maxine started from is in the literature, in parts

**Algebra and coalgebra meet in distributive laws.**
- Turi and Plotkin show that rules in GSOS format are a distributive law of syntax
  over behaviour.
- Two consequences follow:
  - the semantics by initial algebra and by final coalgebra agree;
  - bisimilarity is a congruence, by naturality, without a per-calculus proof.
- The line runs from Plotkin's SOS, which began as reduction semantics, through
  rule formats, Aczel–Mendler, Rutten and Beck, to Turi–Plotkin. After them come
  Lenisa–Power–Watanabe and Klin's survey, and then higher-order abstract GSOS
  (Goncharov, Milius, Schröder, Tsampas, Urbat 2023–26), which treats **SKI**.
  See 13.A and 13.C.

**Observation as a pairing is a logical connection.**
- Our pairing and lenses are Chu(Set, 2) and its morphisms.
- Klin (CMCS 2010) states Chu(Set, 2) = (Set↓2^−).
- Pavlovic, Mislove and Worrell (2006) frame testing as Σ × Θ → Ω.
- Compositionality of logics with respect to SOS (Klin, LICS 2007; Fokkink, van
  Glabbeek, de Wind 2006) is our `put` through contexts.
- T^⊥ is Pitts's ⊤⊤ and Krivine's orthogonality.
- "More observers, finer equality" through a Galois connection is van Glabbeek's
  spectrum, and Beohar, Gurke, König and Messing (CSL 2023) for metrics.
- See 13.B.

**Bisimulation as lifting with existence only** is known: open maps (Joyal, Nielsen,
Winskel), with weak factorization systems in Kurz–Rosický and Hirschowitz–Lafont.

### What appears to be ours [inferred; absence searched for, not proved]

1. **Invariant observation along a category of runs.** Behaviours are functors out of
   the *localization* at the steps. This differs from bisimilarity: it identifies terms
   in one fibre, so it agrees with bisimilarity only for deterministic systems. Turi and
   Plotkin leave "the reductional approach" open. Klin's survey has no reduction
   semantics. No bialgebraic treatment found makes runs a category with 2-cells.
2. **One chain of observer classes** gives syntax, conversion and contextual equivalence
   as three equalities.
3. **Unique against non-unique lifting in one category of runs.** The algebraic,
   orthogonal half is the framework. The coalgebraic, weak half is open maps.
   - For deterministic reduction the two coincide.
   - Non-uniqueness appears with nondeterministic reduction, which is where Lévy's
     2-cells live.

   *Conjecture:* modulo permutation equivalence, lifts are unique up to 2-cells.
4. **Theorem B** (simulations induce adjunctions) speaks to an open problem named in
   both Klin's survey and the higher-order papers: morphisms of distributive laws, for
   translations and compilers.
5. **Runs with 2-cells as intensional structure**: Lévy squares, ℤ-valued holes, cost as
   a Dehn function. The final coalgebra erases these. Polygraphs (Guiraud–Malbos) and
   2-categorical rewriting (Hirschowitz 2013) have the 2-cells but no observation
   theory.

### Where to generalize, in order of payoff

1. **Rule formats for presentations.**
   - Generate the steps of a presentation by an abstract (higher-order) GSOS law.
   - Then derive congruence of sameness under probes from naturality, instead of
     per-calculus proofs (`probeEq_plug` for SKI and tree calculus).
   - Our `Calculus` layer is the elementary shadow of this.
2. **Compare equalities on SKI.**
   - Our probe equivalence and conversion, against strong and weak applicative
     bisimilarity in the higher-order papers.
   - A concrete, checkable test of where the localization and the final coalgebra
     agree.
3. **V-valued pairings.**
   - Lawvere distances and Isbell conjugation for directed observers: cost, traces.
   - Tools: Beohar et al.'s Galois connections, codensity lifting, Gavazzo's
     applicative distances.
   - The lax middle already has two models: lax bialgebras (weak similarity) and lax
     orthogonal factorization systems (Clementino–López Franco).
4. **Lenses as delta lenses.**
   - Clarke's construction turns an orthogonal factorization system and an idempotent
     comonad into an algebraic weak factorization system whose right maps are delta
     lenses.
   - Compare with our Chu lenses on (E, M).
5. **Holes as coverings.** Dubut, Goubault and Goubault-Larrecq's unfolding as a
   universal covering, and Guiraud–Malbos homotopy bases, are language for the ℤ-valued
   hole of ω ω.

### For essay 2

The centre:
- Invariant observers (algebra: what a term equals) against observers that see
  direction (coalgebra: what a term does).
- Distributive laws as the place they meet.
- The framework's addition: runs form a category with 2-cells, so the meeting can be
  studied one level up, where unique and non-unique lifting sit side by side.

The examples: SKI, tree calculus and interaction nets.

## 13.A The lineage from SOS to Turi–Plotkin

### Sources (DOIs checked to resolve)

**Plotkin, *A structural approach to operational semantics***
- Aarhus DAIMI FN-19 (1981). JLAP 60–61 (2004), https://doi.org/10.1016/j.jlap.2004.05.001.
- *The origins of SOS*, https://doi.org/10.1016/j.jlap.2004.03.009.
- [read] Definition 1 is an *unlabelled* transition system: configurations with a
  transition relation, whose steps are "occurrences of operations". Reduction is said
  to originate in λ-calculus; labelled systems come later (§1.3.4). SOS began as
  reduction semantics.

**Rule formats**
- de Simone, TCS 37 (1985), https://doi.org/10.1016/0304-3975(85)90093-3 [not read].
- Bloom, Istrail and Meyer, *Bisimulation can't be traced*, JACM 42 (1995),
  https://doi.org/10.1145/200836.200876 [abstract]. GSOS. The congruence induced by
  completed traces under GSOS contexts is ready simulation.
- Groote and Vaandrager, Inf. & Comp. 100 (1992),
  https://doi.org/10.1016/0890-5401(92)90013-6. With tyft/tyxt rules, bisimulation is a
  congruence. Congruence is a property of the shape of the rules.

**Coalgebra**
- Aczel and Mendler, CTCS '89, https://doi.org/10.1007/BFb0018361 [not read]. Bisimulation
  as a span of coalgebra maps.
- Rutten, *Universal coalgebra*, TCS 249 (2000),
  https://doi.org/10.1016/S0304-3975(00)00056-6. The algebra/congruence and
  coalgebra/bisimulation duality.
- Jacobs and Rutten, tutorial (2011), https://doi.org/10.1017/CBO9780511792588.003.

**Distributive laws**
- Beck, *Distributive laws*, LNM 80 (1969), https://doi.org/10.1007/BFb0083084.
- Turi–Plotkin Thm 7.1 [read]. For a monad T and a comonad D, these are equivalent:
  - distributive laws TD ⇒ DT;
  - liftings of T to D-coalgebras;
  - liftings of D to T-algebras.

**Turi and Plotkin, *Towards a mathematical operational semantics***
- LICS 1997, 280–291, https://doi.org/10.1109/LICS.1997.614955 [read].
- Thm 1.1: image-finite GSOS rule sets are natural transformations
  Σ(X × (P_f X)^A) → (P_f TX)^A, and naturality explains their good behaviour.
- Abstract GSOS is ρ : Σ(Id × B) ⇒ BT. It gives an operational monad on B-coalgebras.
  Dually, a denotational comonad on Σ-algebras.
- Models are λ-bialgebras TX → X → DX.
  - There is an initial model (operational) and a final model (denotational).
  - The unique map between them is both the initial-algebra and the final-coalgebra
    semantics: "universal semantics".
  - It is fully abstract for bisimulation if B preserves weak pullbacks (Cor 7.4).
  - Bisimilarity is a congruence (Cor 7.5).
- For B = (P_f)^A, coalgebra maps are the P-open maps of Joyal–Nielsen–Winskel
  (LICS 1993, https://doi.org/10.1109/LICS.1993.287566).
- Limits they state:
  - weak bisimulation only indirectly;
  - binders (λ, π) are future work;
  - "the relationship between the transitional approach considered here and others,
    such as the reductional one arising in the λ-calculus and term-rewriting" is left
    open.

**Turi's thesis and after**
- Turi, *Functorial operational semantics and its denotational dual*, PhD thesis, **Vrije
  Universiteit Amsterdam, 1996**, https://ir.cwi.nl/pub/17102/17102B.pdf.
  - Ch. 8 "Operational is denotational".
  - Ch. 13 "The observational comonad for bisimulation".
- Rutten and Turi, REX '93, https://doi.org/10.1007/3-540-58043-3_28.
- Plotkin, *Bialgebraic semantics and recursion*, CMCS 2001,
  https://doi.org/10.1016/S1571-0661(04)80914-9 [read]. With recursion over cppos, weak
  pullbacks and full abstraction fail. The move is from spans to relations and
  simulations.
- Lenisa, Power and Watanabe, CMCS 2000, https://doi.org/10.1016/S1571-0661(05)80350-0.
  GSOS is a distributive law of a monad over a copointed endofunctor.
- Lenisa, Power and Watanabe, TCS 327 (2004), https://doi.org/10.1016/j.tcs.2004.07.024.
- Klin, *Bialgebras for structural operational semantics: an introduction*, TCS 412
  (2011), https://doi.org/10.1016/j.tcs.2011.03.023 [read]. Open problems he lists:
  - completeness of rule formats;
  - rules for general laws;
  - the many equivalences beyond bisimilarity;
  - **morphisms of distributive laws for translations ("little has been done")**;
  - going beyond GSOS (Staton, LICS 2008, https://doi.org/10.1109/LICS.2008.43).

  The survey does not treat reduction semantics or weak bisimulation.
- Reaction rules to labels: Leifer and Milner, CONCUR 2000,
  https://doi.org/10.1007/3-540-44618-4_19, and Sewell, TCS 274 (2002),
  https://doi.org/10.1016/S0304-3975(00)00309-1. Labels are derived as minimal enabling
  contexts, so that bisimilarity is a congruence. This is the closest analogue of probes
  as contexts.

**Higher-order abstract GSOS**
- Goncharov, Milius, Schröder, Tsampas and Urbat, POPL 2023,
  https://doi.org/10.1145/3571215; JFP version https://doi.org/10.46298/jfp.17738. **SKI**
  with behaviour B(X, Y) = Y + Y^X: either a reduction step, or a function of a supplied
  term.
- Follow-ups:
  - weak similarity, LICS 2023, https://doi.org/10.1109/LICS56636.2023.10175706;
  - logical predicates, FoSSaCS 2024, https://doi.org/10.1007/978-3-031-57231-9_3;
  - step-indexed logical relations sound for contextual equivalence, LICS 2024,
    https://doi.org/10.1145/3661814.3662099.

### What we re-found, and what is ours [inferred unless marked]

| Ours | Theirs |
|---|---|
| contextual equivalence is a congruence (proved per calculus) | Cor 7.5 (follows from the format, by naturality) |
| denotation as reflection | universal semantics (the initial model to the final model) |
| coalgebraic equality as lifting with existence only | already known: open maps (JNW), coalgebra maps = P-open maps [read] |

- **Our behaviours do not match the final coalgebra.** Ours come from a localization:
  steps are inverted, so terms in one fibre are equal. Theirs identify bisimilar terms.
  The two agree only for deterministic systems.
- **The new part of the lifting conjecture** is the *unique*-lifting (orthogonal)
  half, and putting the two halves in one category of runs.
- **Theorem B speaks to Klin's open problem** on morphisms of distributive laws for
  translations.
- **Not there:** orthogonal factorization systems, the localization, Chu observation and
  T^⊥ types, lenses, runs as a category with 2-cells (Lévy), cost as a Dehn function, and
  a bialgebraic treatment where runs form a category.
- **Reduction vs coalgebra.** Plotkin's transition relation is a powerset coalgebra Γ →
  PΓ. Our category of runs is the free category on that graph, cut down by 2-cells. The
  coalgebra is our generating steps without their composition.
- **What they offer us:**
  - congruence from a rule format, not per-calculus proofs;
  - our steps generated by an abstract (higher-order) GSOS law;
  - the full-abstraction machinery.
- **Concrete test:** does our SKI probe equivalence coincide with their applicative
  bisimilarity for SKI?

## 13.B Observation, tests and logics as pairings

### Sources

**Classical observation**
- Morris 1968. Contextual equivalence is "C[M] has a normal form iff C[N] does, for
  every context C". MIT thesis https://hdl.handle.net/1721.1/64850; report MAC-TR-57
  https://hdl.handle.net/1721.1/149376.
- De Nicola and Hennessy, *Testing equivalences for processes*, TCS 34 (1984),
  https://doi.org/10.1016/0304-3975(84)90113-0. Tests are processes with a success
  action; may and must preorders.
- Abramsky, *Observation equivalence as a testing equivalence*, TCS 53 (1987),
  https://doi.org/10.1016/0304-3975(87)90065-X.
- Abramsky and Ong, *Full abstraction in the lazy lambda calculus*, Inf. Comput. 105
  (1993), https://doi.org/10.1006/inco.1993.1044. Applicative bisimilarity is strictly
  finer than contextual equivalence in pure lazy λ. The two coincide once convergence
  testing is added. A textbook case of "more observers, finer equality".
- Howe, Inf. Comput. 124 (1996), https://doi.org/10.1006/inco.1996.0008.
- Hennessy and Milner, JACM 32 (1985), https://doi.org/10.1145/2455.2460.
- van Glabbeek, *The linear time–branching time spectrum I* (2001),
  https://doi.org/10.1016/B978-044482830-9/50019-9. Each equivalence is defined by a class
  of observations; nested classes give nested equivalences.

**Logical connections**
- Pavlovic, Mislove and Worrell, *Testing semantics: connecting processes and process
  logics*, AMAST 2006, https://doi.org/10.1007/11784180_24 [read].
  - Testing is a map Σ × Θ → Ω. A logical connection is a dual adjunction.
  - Thm 1: a distributive law lifts the connection to one between coalgebras and
    algebras.
  - Tests are also processes, which is the symmetric pairing.
- Klin, *Coalgebraic modal logic beyond sets*, ENTCS 173 (2007),
  https://doi.org/10.1016/j.entcs.2007.02.034.
- Bonsangue and Kurz, FoSSaCS 2005, https://doi.org/10.1007/978-3-540-31982-5_29, and
  FoSSaCS 2006, https://doi.org/10.1007/11690634_12.
- Kupke, Kurz and Pattinson, ENTCS 106 (2004),
  https://doi.org/10.1016/j.entcs.2004.02.037.
- Pattinson, TCS 309 (2003), https://doi.org/10.1016/S0304-3975(03)00201-9.
- Schröder, TCS 390 (2008), https://doi.org/10.1016/j.tcs.2007.09.023.
- Jacobs and Sokolova, *Exemplaric expressivity*, JLC 20 (2010),
  https://doi.org/10.1093/logcom/exn093.
- Survey: Kupke and Pattinson, TCS 412 (2011),
  https://doi.org/10.1016/j.tcs.2011.04.023.
- **Klin, CMCS 2010**, https://doi.org/10.1016/j.entcs.2010.07.019 [read]. The closest
  single match.
  - Objects of the slice (D↓F) are (X, Φ, r : Φ → FX).
  - Morphisms are (f : X → Y, g : Ψ → Φ) with Ff∘s = r∘g.
  - It states **Chu(Set, 2) = (Set↓2^−)**: f is our get, g is our put, and the
    condition is our `pass_put`.

**Compositionality with respect to SOS**
- Klin, *Bialgebraic operational semantics and modal logic*, LICS 2007,
  https://doi.org/10.1109/LICS.2007.13 [read]. If the formulas satisfied by f(t₁…tₙ) can
  be derived from those of the tᵢ, logical equivalence is a congruence, via a logical
  distributive law dual to the GSOS law.
- Fokkink, van Glabbeek and de Wind, TCS 354 (2006),
  https://doi.org/10.1016/j.tcs.2005.11.035. Modal decomposition:
  σ(t) ⊨ φ ⇔ ∃ψ ∈ t⁻¹(φ), ∀x, σ(x) ⊨ ψ(x).
- Larsen and Liu, ICALP 1990, https://doi.org/10.1007/BFb0032056, and JLC 1 (1991),
  https://doi.org/10.1093/logcom/1.6.761 [recalled: content not reached].
- Bloom, Fokkink and van Glabbeek, ACM TOCL 5 (2004),
  https://doi.org/10.1145/963927.963929.

**Biorthogonality and logical relations**
- Pitts, MSCS 10 (2000), https://doi.org/10.1017/S0960129500003066 [read]. ⊤⊤-closure
  comes from a Galois connection between term relations and relations on evaluation
  contexts.
- Vouillon and Melliès, POPL 2004, https://hal.science/hal-00150968. The DOI is not yet
  verified.
- Melliès and Vouillon, LICS 2005, https://doi.org/10.1109/LICS.2005.42.
- Krivine, *Realizability in classical logic*, https://hal.science/hal-00154500
  [recalled]. ‖A→B‖ = {u·π | u ⊩ A, π ∈ ‖B‖}.
- Girard, TCS 50 (1987), https://doi.org/10.1016/0304-3975(87)90045-4.
- Pratt, Coimbra notes, http://boole.stanford.edu/pub/coimbra.pdf; APAL 96 (1999),
  https://doi.org/10.1016/s0168-0072(98)00043-8.
- Tait, JSL 32 (1967), https://doi.org/10.2307/2271658.
- Plotkin 1973, SAI-RM-4.
- Statman, Inf. Control 65 (1985), https://doi.org/10.1016/S0019-9958(85)80001-2.
- Katsumata, CSL 2005, https://doi.org/10.1007/11538363_8.
- Lindley and Stark, TLCA 2005, https://doi.org/10.1007/11417170_20.

**Quantitative and directed observation**
- Baldan, Bonchi, Kerstan and König, LMCS 14(3) 2018,
  https://doi.org/10.23638/LMCS-14(3:20)2018.
- **Beohar, Gurke, König and Messing, *Hennessy–Milner theorems via Galois connections*,
  CSL 2023**, https://doi.org/10.4230/LIPIcs.CSL.2023.12. The closest existing form of
  "observer classes give equalities through a Galois connection". It covers metrics and
  directed trace metrics.
- Katsumata and Sato, CALCO 2015, https://doi.org/10.4230/LIPIcs.CALCO.2015.156.
- Komorida, Katsumata, Hu, Klin and Hasuo, LICS 2019,
  https://doi.org/10.1109/LICS.2019.8785691. Codensity lifting is ⊤⊤ over an object Ω of
  truth values.
- König and Mika-Michalski, CONCUR 2018, https://doi.org/10.4230/LIPIcs.CONCUR.2018.37.
- Forster et al., CSL 2023, https://doi.org/10.4230/LIPIcs.CSL.2023.22.
- Gavazzo, LICS 2018, https://doi.org/10.1145/3209108.3209149.
- Dal Lago, Gavazzo and Levy, LICS 2017, https://doi.org/10.1109/LICS.2017.8005117.
- Hasuo, Jacobs and Sokolova, LMCS 3(4) 2007, https://doi.org/10.2168/LMCS-3(4:11)2007.
- Pavlovic, *Quantitative concept analysis*, ICFCA 2012,
  https://doi.org/10.1007/978-3-642-29892-9_24.

### What we re-found

| Ours | Already there |
|---|---|
| pairing and lens | Chu(Set, 2) and Chu morphisms (Pratt); Klin 2010's slice description; Pavlovic–Mislove–Worrell's logical connection |
| `Lens.preimage_orth` | Klin's morphism condition; single-valued modal decomposition |
| sameness is a congruence when lenses are contexts | Klin LICS 2007; Pitts's ⊤⊤ |
| T^⊥ and arrow types | Pitts's ⊤⊤; Krivine's ‖A→B‖ |
| larger observer class, finer equality | van Glabbeek; Abramsky 1987; Abramsky–Ong; Beohar et al. |
| lens types cannot express "runs to I" | biorthogonal sets are saturated under observational equivalence (standard) |

Where our version differs:
- Our `put` is single-valued because observers are themselves contexts, so that
  `put` is composition, as in Morris and Pitts.
- The SOS decomposition line needs sets of decompositions, a disjunctive or relational
  `put`, because its observers are formulas in a fixed logic.

### Apparently new [inferred; searched, absence not proved]

- One chain of observer classes giving syntax, conversion and contextual equivalence.
  Each piece is standard; the chain is not.
- Invariance of a pairing along a category of reduction steps, with behaviours as
  functors out of the localization. Meseguer's rewriting logic, TCS 96 (1992),
  https://doi.org/10.1016/0304-3975(92)90182-F, treats rewriting as a category but
  builds no observation theory on it.
- Probes packaged as a lens theory, with `put` as composition, beside the SOS
  decomposition line.
- **Caveat to state.** A Prop-valued invariant pairing factors through π₀ of the
  localization. The categorical structure is invisible to two-valued observers. It shows
  only for Set- or groupoid-valued observers, or for directed V-valued ones.

### Generalizing to V-valued pairings [inferred]

Take `pass : D × O → V` for a quantale V, with the lens condition unchanged.
- T^⊥(d) = ⋀_o [T(o), pass(d, o)] is Isbell conjugation.
- Sameness becomes a directed Lawvere distance:
  δ(d₁, d₂) = ⋀_o [pass(d₁, o), pass(d₂, o)].
- `get` is non-expansive, which generalizes `Lens.same`.
- get*(T^⊥) = (put_! T)^⊥, where put_! is the left Kan extension.
- A directed observer has a step act by a V-morphism instead of a bijection.

Tools to build on:
- Beohar et al. (Galois connections);
- codensity lifting;
- Gavazzo's applicative distances, for SKI-style higher-order calculi;
- Barr's Chu(V, K).

## 13.C After Turi–Plotkin: higher order, 2-cells, and lifting

### Higher-order mathematical operational semantics (HO-MOS)

**Goncharov, Milius, Schröder, Tsampas and Urbat**
- POPL 2023, https://doi.org/10.1145/3571215; JFP 36 (2026),
  https://doi.org/10.46298/jfp.17738, arXiv:2405.16708 [read].
- The law is ρ : Σ(jX × B(jX, Y)) → B(jX, Σ*(jX + Y)), dinatural in X.
- If C is regular, Σ preserves reflexive coequalizers and B preserves monos, the kernel of
  μΣ → Z is a congruence. A final bialgebra generally does not exist.
- **SKI** is treated as xCL, with S′, K′ and S″ added, B(X, Y) = Y + Y^X, and a
  deterministic head strategy. The equality is *strong* (step-counting) applicative
  bisimilarity.
- Their hand proof of congruence for xCL notes that bisimulation up to transitive closure
  "could have been avoided by working with multi-hole contexts". That is our probe
  design.
- Open problem in the JFP conclusion: morphisms of higher-order GSOS laws (compilers).

**Follow-ups**
- Goncharov, Santamaria, Schröder, Tsampas and Urbat, *Logical predicates in HO-MOS*,
  FoSSaCS 2024, https://doi.org/10.1007/978-3-031-57231-9_3 [read].
  - Logical predicates are coalgebraic invariants: predicates closed under the
    coalgebra.
  - The main application is strong normalization of simply typed xCL.
  - Caveat: for *untyped* CL the canonical lifting is not contractive, and the fixed point
    may not exist.
  - Remark: CL with any redex reducible gives a nondeterministic law over 𝒫B.
- Urbat et al., *Weak similarity in HO-MOS*, LICS 2023,
  https://doi.org/10.1109/LICS56636.2023.10175706 [read]. An abstract Howe's method.
  Congruence needs the operational model to be a **lax bialgebra**.
- Goncharov, Milius, Tsampas and Urbat, LICS 2024,
  https://doi.org/10.1145/3661814.3662099. Step-indexed logical relations, sound for
  contextual equivalence when the weak model is a lax bialgebra. Combinatory logics are
  instances.
- Later work:
  - call-by-push-value, POPL 2025, https://doi.org/10.1145/3704871;
  - stateful languages, ICFP 2025, https://doi.org/10.1145/3747513;
  - Urbat, behavioural conformances via fibrations (metrics), POPL 2026,
    https://doi.org/10.1145/3776697;
  - Goncharov, Peressotti, Tsampas, Urbat and Volpe, bialgebraic denotational semantics,
    ICFP 2026, https://doi.org/10.1145/3828693.

**Factorization-system approaches**
- **Hirschowitz and Lafont**, LMCS 18(3:37) 2022,
  https://doi.org/10.46298/lmcs-18(3:37)2022 [read].
  - They drop Turi–Plotkin coalgebraic bisimulation "in favour of a notion based on
    factorisation systems, similar to Joyal et al.".
  - A functional bisimulation is a map with the right lifting property (existence only)
    against a source map in a presheaf transition category.
  - Congruence by an abstract Howe's method, with conditions from weak factorization
    systems.
- Precursors: Hirschowitz, POPL 2019, https://doi.org/10.1145/3290334, and EPTCS 300
  (2019), https://doi.org/10.4204/EPTCS.300.1.
- Fiore, Plotkin and Turi, LICS 1999, https://doi.org/10.1109/LICS.1999.782615. Fiore and
  Turi, LICS 2001, https://doi.org/10.1109/LICS.2001.932486. DOIs only.

### 2-categorical rewriting

- Hirschowitz, LMCS 9(3:10) 2013, https://doi.org/10.2168/LMCS-9(3:10)2013 [read].
  - In the free cartesian closed 2-category on a 2-signature, 2-cells are proof terms
    modulo permutation equivalence, soundly and completely.
  - Calculi with structural congruence need "2-theories" that add equations between
    reductions. This is close to our equations as 2-cells.
  - He credits Hilken with the view that computational behaviour is the non-invertible
    2-cells.
- Hilken, TCS 170 (1996), https://doi.org/10.1016/S0304-3975(96)00097-7.
- Seely, LICS 1987: no DOI found, not read.
- Fiore and Saville, MSCS 31 (2021), https://doi.org/10.1017/S0960129521000281. Their
  2-cells are structural, not reductions.
- Squier, Otto and Kobayashi, TCS 131 (1994), https://doi.org/10.1016/0304-3975(94)90175-9.
- Guiraud and Malbos, MSCS 28 (2018), https://doi.org/10.1017/S0960129516000220.
  Homotopy bases are generated by critical branchings, which is our "holes filled by
  equations". *Polygraphs*, CUP 2025, https://doi.org/10.1017/9781009498968.
- **Nothing found** that connects permutation 2-cells to bialgebraic semantics. HO-MOS
  fixes a strategy and has no 2-cells.

### Lifting and factorization for bisimulation

- Joyal, Nielsen and Winskel, Inf. & Comp. 127 (1996),
  https://doi.org/10.1006/inco.1996.0057.
- Kurz and Rosický, ACS 13 (2005), https://doi.org/10.1007/s10485-004-6730-z [snippet
  only]. They treat open maps as a weak factorization system (L, OP), and contrast the
  homotopy category of a weak factorization system with a localization.
- Lasota, TCS 280 (2002), https://doi.org/10.1016/S0304-3975(01)00023-8.
- Wißmann, Dubut, Katsumata and Hasuo, FoSSaCS 2019,
  https://doi.org/10.1007/978-3-030-17127-8_30.
- Dubut, Goubault and Goubault-Larrecq, CONCUR 2016,
  https://doi.org/10.4230/LIPIcs.CONCUR.2016.25: the unfolding is a universal covering.
  The same authors, ICALP 2015, https://doi.org/10.1007/978-3-662-47666-6_14.
- Algebraic weak factorization systems:
  - Grandis and Tholen 2006, https://eudml.org/doc/249802.
  - Garner, ACS 17 (2009), https://doi.org/10.1007/s10485-008-9137-4. Not the
    retracted duplicate ending -9126-7.
  - Bourke and Garner, JPAA 220 (2016), https://doi.org/10.1016/j.jpaa.2015.06.002.
  - Bourke, JPAA 227 (2023), https://doi.org/10.1016/j.jpaa.2022.107294.
- **Clarke, *The AWFS for delta lenses*, EPTCS 397 (2023),
  https://doi.org/10.4204/EPTCS.397.4.** Its R-algebras are delta lenses, functors with
  chosen lifts. The construction works for any orthogonal factorization system with an
  idempotent comonad, so it may apply to our (E, M).
- Clementino and López Franco, *Lax orthogonal factorisation systems*, Adv. Math. 302
  (2016), https://doi.org/10.1016/j.aim.2016.07.028.
- **Nothing found** that connects algebraic weak factorization systems to operational
  semantics.

### Corrections to our §12.8 guess [inferred]

- "Bisimulation is lifting with existence only" is **known**: Joyal–Nielsen–Winskel,
  Kurz–Rosický, Hirschowitz–Lafont.
- What is not stated anywhere found: invariant equality as the orthogonal
  (unique-lifting) system and bisimulation as the weak one, *in one category of runs*.
- The algebraic weak factorization system's own comonad–monad pair lives on the arrow
  category. It is not Turi–Plotkin's syntax/behaviour law, so "algebra meets coalgebra"
  is not literally that structure. Its R-algebras are open maps with chosen lifts.
- **For deterministic reduction, lifts are unique, and the two halves coincide.**
  Non-uniqueness appears only with nondeterministic reduction, which is exactly where
  Lévy's 2-cells live.

  *Testable conjecture:* quotienting runs by permutation equivalence restores
  uniqueness of lifts up to 2-cells.
- Their **strong** applicative bisimilarity counts steps, so it is a directed observer.
  Weak similarity is nearer to our invertible-step equality.
- **The lax middle** already has two models: their lax bialgebras and lax orthogonal
  factorization systems.
