# R1 C · Literature references

Reviewed the frozen essay at `7626ff8`. Its bytes match the working-tree essay.
The normal-derivation theorem supports the SKI example under residual equivalence. The prose describes a narrower rule for identifying runs.
The Church–Turing, interaction-net and coherence passages need more precise statements of what their references establish.
The appendix inventories the sidenote references and records metadata, source checks and unresolved lookups.

## Atoms and Probes · opening and calculus switch

### C1 — Source the rules where the alternate calculi first appear

- **Location** — Atoms and Probes, “has one constant, the leaf” and “joined at their principal ports.”
- **Problem** — The switch introduces two external calculi without nearby literature references. The Lean links address the particular tree system or compilation. The tree book and Lafont appear much later, and the book uses the earlier presentation of the tree rules.
- **Severity** — should
- **Suggested fix** — Put a sidenote by each legend. Cite the small-step semantics of the [current tree-calculus specification](https://treecalcul.us/specification/) for the five schemes and Lafont’s [Interaction nets](https://doi.org/10.1145/96709.96718) for agents, principal ports and interactions. Retain the compilation credit for the fifteen-rule table. If “values” means closed normal forms, say that `u` and `v` are themselves values.

## Atoms and probes

### C2 — Qualify the Morris attribution

- **Location** — Atoms and probes, “Morris observes only whether a run ends.”
- **Problem** — The thesis citation has no locator for the claim that its observation is termination alone. The contextual construction is the relevant precedent for the essay’s observation choice, and the narrower historical gloss remains unconfirmed.
- **Severity** — should
- **Suggested fix** — Say “Morris compares terms by placing them in contexts. Here the observation is a readback built only from the context’s own variables.” Link the [MIT thesis record](https://hdl.handle.net/1721.1/149376) and give the page for any more specific characterization of Morris’s chosen test.

### C3 — Limit the interaction-net cost result

- **Location** — Atoms and probes, “any two runs between the same nets have the same length.”
- **Problem** — Lafont’s one-step diamond supports equal lengths for completed runs to an irreducible net. The cited result does not give equal lengths for arbitrary endpoints. A system can satisfy a one-step diamond and admit a return to a previous state. The same overreach appears in the net note near the counter.
- **Severity** — block
- **Suggested fix** — Say “Every run from this starting net to an irreducible net takes the same number of interactions.” Cite [Lafont 1997](https://doi.org/10.1006/inco.1997.2643), §1.2, Proposition 1 and the paragraph that follows. For the counter note, either supply a separate proof for the particular reachable nets or restrict the conclusion to runs that finish.

## Running a term

### C4 — Describe what the denotational source actually models

- **Location** — Running a term, “A program denotes a value, and a type sorts programs by their values.”
- **Problem** — Scott and Strachey’s denotational account includes mathematical objects such as functions on stores and continuations. PRG-6 does not equate denotation with an operational normal form or derive its semantics by collapsing the essay’s fibres.
- **Severity** — block
- **Suggested fix** — Say “This last view gives each terminating term its normal form as a denotation. Denotational semantics more generally assigns a mathematical meaning to a program.” Cite the [PRG-6 abstract and introduction](https://www.cs.ox.ac.uk/files/3228/PRG06.pdf) for the latter, and present the reduction-fibre construction as the essay’s example.

## Three equalities

### C5 — Source the claims about type checkers and `η`

- **Location** — Three equalities, “A proof assistant decides this equality by running both sides” and “most checkers leave them to be proved.”
- **Problem** — Sidenote 10 supports the terminology for contextual equivalence. Sidenote 12 gives normalization by evaluation for a particular simply typed calculus with coproducts. Neither establishes the general claims about conversion algorithms or how often implementations make function, record, sum and natural-number `η` judgmental. Note 11 also needs a section for the bracket-abstraction claim.
- **Severity** — should
- **Suggested fix** — Use named examples of conversion and judgmental `η`, with a manual section for each, or state the conditional result for the essay’s calculus. Keep Altenkirch et al. for their coproduct algorithm. Cite a section on bracket abstraction in Curry–Feys or Barendregt beside “bound variables compiled away.”

## Types

### C6 — Give a source for the exact saturated-set condition

- **Location** — Types, “Tait’s saturated sets are closed under head expansion.”
- **Problem** — The note gives the historical 1967 reference without a locator for this modern formulation. Expansion usually comes with side conditions on the terms being inserted. The opening “Every account” is broader than the four cited examples.
- **Severity** — should
- **Suggested fix** — Name the precise saturation definition and its side conditions or say “In a standard saturated-set formulation of Tait’s method, suitable head expansions preserve membership.” Pin reducibility candidates to Girard’s chapter 14, under the candidate conditions, and identify which closure operation the biorthogonal citation is being used for.

## The definition

### C7 — Identify the generating maps for the factorization-system citation

- **Location** — The definition, “The steps generate an orthogonal factorization system on the category of families”
- **Problem** — The references name a general construction. A step is a morphism in the run category, whereas the orthogonality generators must be morphisms in the functor category.
- **Severity** — could
- **Suggested fix** — Add “For a step `s → t`, use the induced map of covariant representables `Hom(t,−) → Hom(s,−)` as a generator.” Then cite [Freyd–Kelly](https://doi.org/10.1016/0022-4049(72)90001-1) for the small-generation argument.

## What a type cannot see

### C8 — Tie the cost theorem to its calculus and evaluation strategy

- **Location** — What a type cannot see, “this number is a fair measure of cost”
- **Problem** — The result cited proves a polynomial simulation for leftmost-outermost β-reduction in the λ-calculus under its input and evaluation conventions. The demonstrative “this number” refers to the preceding SKI example and gives the impression the same theorem covers its step count.
- **Severity** — block
- **Suggested fix** — Say “For the λ-calculus, Accattoli and Dal Lago prove that counting leftmost-outermost β-steps gives a polynomially invariant time measure.” Keep the SKI count as a cost definition unless a separate machine simulation covers it. [Published paper](https://doi.org/10.2168/LMCS-12(1:4)2016)

### C9 — Name the rewriting result in place of an unsupported priority claim

- **Location** — What a type cannot see, “The general study of equations between runs begins with”.
- **Problem** — Squier, Otto and Kobayashi study finite derivation type for string-rewriting presentations of monoids. Their paper supports a connection with confluence equations, within that setting. It does not establish priority for the general study or analyze the essay’s bracketing calculus.
- **Severity** — should
- **Suggested fix** — Say “For string rewriting, Squier, Otto and Kobayashi relate finite convergent presentations to finite derivation type.” Cite their Theorems 5.2–5.3 for generating confluences and finite derivation type, as restated in Guiraud–Malbos, Theorems 4.3.2–4.3.3. [Original article](https://doi.org/10.1016/0304-3975(94)90175-9), [later explicit formulation](https://doi.org/10.1017/S0960129516000220)

## When probes can read atoms

### C10 — Pin the tree sources to versions and claims

- **Location** — When probes can read atoms, “the specification on the tree calculus website” and “what can and cannot be translated”.
- **Problem** — Note 17 leaves the specification as a description. The book is a source for structural inspection and needs an edition or stable link and a triage locator. The arXiv preprint compares models using an encoding-sensitive notion of computational equivalence. The vague translation gloss obscures that scope and the citation lacks a version.
- **Severity** — should
- **Suggested fix** — Link the [specification](https://treecalcul.us/specification/) beside the shape cases and identify the book by the edition and its triage discussion. Cite [arXiv:1410.7103](https://doi.org/10.48550/arXiv.1410.7103) with the version used, beside a statement about the preprint’s particular equivalence criterion. Place the same section of the specification or a precise equality-program reference beside “Equality of code is a program” in the Types alternate figure note.

## Changing the ingredients

### C11 — State the Church–Turing thesis separately from the equivalence proofs

- **Location** — Changing the ingredients, “No calculus with finite descriptions and finitely many local rules has since been found to add a point, and the Church–Turing thesis is the claim that none will.”
- **Problem** — The cited equivalence theorems compare particular formal models. Church’s §7 identifies effective calculability with recursiveness or λ-definability, and Turing’s 1936–37 paper argues for his analysis of what a human can compute by a rule. Neither makes the quoted claim about every system described by finitely many local rules. Such a formal simulation claim needs effective representations of configurations and transitions, an effective readout, and a convention for outcomes.
- **Severity** — block
- **Suggested fix** — Say “Using standard representations of numbers, these models compute the same partial numerical functions. The Church–Turing thesis identifies effective calculability with Turing computability.” Cite Church §7 for the thesis, Kleene for the λ-definability/recursiveness directions, and Turing’s 1937 JSL paper for the machine/λ equivalence. Explicitly distinguish the original total-function or sequence formulations from the modern partial-function presentation. Apply the same qualification to the first card and Summary. [Church](https://doi.org/10.2307/2371045), [Kleene](https://doi.org/10.1215/S0012-7094-36-00227-2), [Turing](https://doi.org/10.2307/2268280)

### C12 — Remove or source the historical and priority glosses

- **Location** — Changing the ingredients, “proposed independently in the 1930s by Church, Kleene and Turing” and “whose conclusions are disputed.”
- **Problem** — Church §7 credits Kleene in the equivalence work, and Turing’s JSL opening credits the Church/Kleene result used in his proof. “Independently” blurs that relationship. The dispute note gives no critic or disputed proposition. Likewise, the sources do not establish why the usual notion is “commonly taken” for the whole subject.
- **Severity** — should
- **Suggested fix** — Say “In the 1930s, Church and Kleene related λ-definability to recursiveness, and Turing introduced a machine model and related it to λ-definability.” Delete the unsourced reception language or cite a specific published account. For note 20, name and cite the exact rebuttal if the qualification stays. Keep Boker–Dershowitz for encoding-sensitive comparison and Felleisen for comparison by expressibility under specified translations.

### C13 — Put sources by the individual card results

- **Location** — Changing the ingredients, “Calculi that agree on numbers disagree here” “Bisimulation is defined by a lifting condition of the kind in note 14” and “the least number of steps between two words is the area between their paths.”
- **Problem** — The shared note gives a whole higher-order computability book without an example, blurs open maps’ existence of lifts with note 14’s unique lifting, and gives no specific source or derivation for the illustrated grid area. The general group area reference concerns a different statement.
- **Severity** — should
- **Suggested fix** — Cite a particular higher-type separation from Longley–Normann beside the higher-type card. Say “Open maps have the path-lifting property. Bisimilarity is characterized by a span of open maps,” citing the opening definition and labelled-transition-system example in [Joyal–Nielsen–Winskel](https://doi.org/10.1006/inco.1996.0057). Put Lafont beside the net-cost card and Hofmann–Streicher beside the proof card. For monotone grid paths give the one-line inversion count: each adjacent swap moves across one cell, and swapping toward the target removes one intervening cell per step.

### C14 — Use residual equivalence in the normal-derivation claim

- **Location** — Changing the ingredients, “runs differing only in the order of independent steps are counted as one run.”
- **Problem** — Huet–Lévy I, Theorem 3.26, supports the claim for permutation equivalence of coinitial finite derivations to a normal form. That equivalence also accounts for erasing and duplicating residuals. Swapping independent steps alone preserves length and cannot identify the displayed one- and two-step runs. Van Oostrom–de Vrijer’s Theorem 7.1 equates four specified definitions. Remark 7.6(i) qualifies the labelling correspondence for collapsing rules, including SKI’s I and K rules. The paper does not identify the essay’s mechanized equations with its own definitions.
- **Severity** — block
- **Suggested fix** — Say “Count runs using Lévy’s permutation equivalence. When a step erases an argument, a step inside it leaves no residual. When a step copies it, a step inside it may leave several. Huet and Lévy’s normal derivation theorem then puts all runs from a given term to its normal form in one class.” Retain the caveat in Mechanized and carry it into this passage if the Lean quotient is meant here. Reference Part I, §3, Theorem 3.26, and cite Theorem 7.1 with Remark 7.6(i) of [Four equivalent equivalences of reductions](https://doi.org/10.1016/S1571-0661(04)80599-1) for the four characterizations. If retaining the original attribution, add Lévy’s *Réductions correctes et optimales dans le λ-calcul*, state doctorate, Université Paris VII, 1978, cited as reference 24 by van Oostrom and de Vrijer.

### C15 — Keep observations about the eager net distinct from general net theory

- **Location** — Changing the ingredients, “in the first thousand interactions no net comes round again” and “There is no loop for a hole to be in.”
- **Problem** — No cited general interaction-net result rules out recurrence of this compiled starting net. The stated bounded observation cannot establish the conclusion. The earlier “its net never stops growing” and the counter note repeat the unqualified claim. Likewise, the 27-interaction lazy example is a fact about a specific compiler and run, outside Lafont’s results.
- **Severity** — should
- **Suggested fix** — Credit the supplied reducer or a pinned trace beside the growth and cost examples. Say “The displayed net run has no repeated state through the first 1,000 interactions” if that is the extent of the check. For an all-orders claim supply the specific growth invariant or a theorem for the eager compiler. Give the specific lazy table and trace or theorem for the 27 interactions beside the earlier illustration.

## Summary

### C16 — State the scope of the coherence result

- **Location** — Summary, “proves a coherence theorem for such runs when they are invertible.”
- **Problem** — Hilken treats a specific directed typed calculus of β-reductions and η-expansions subject to equations. Fiore–Saville, Theorem 1.1, concerns parallel structural 2-cells in a free cartesian closed bicategory on a set. Inverting arbitrary runs, including Hilken’s, is insufficient as a description of that theorem.
- **Severity** — block
- **Suggested fix** — Say “Hilken studies equations between rewrites in the simply typed 2λ-calculus. Fiore and Saville prove that parallel structural 2-cells in a free cartesian closed bicategory coincide.” Cite [Hilken’s published article](https://doi.org/10.1016/S0304-3975(96)80713-4) and [Fiore–Saville, Theorem 1.1](https://doi.org/10.1145/3373718.3394769).

### C17 — Add links and correct bibliographic details

- **Location** — Summary, “Three works stand close to this one” and the other notes listed in the appendix.
- **Problem** — Most DOI-bearing works are given as plain text. Even the three DOI identifiers in the normal-derivation sidenote lack clickable DOI links. Several bare book or report references lack stable identifiers. Note 21’s Novikov reference lacks a title and venue. Boker–Dershowitz ends at p. 647. OUP gives pp. 83–112 for the DOI-linked Hofmann–Streicher chapter. The appendix identifies titles to complete and alternative editions to distinguish.
- **Severity** — should
- **Suggested fix** — Apply the DOI links and identifier corrections in the appendix. Use an ISBN or stable institutional link for a book without a DOI, and stable archive links for reports and theses. Expand Novikov to the full 1955 record.

## Appendix · Sidenote inventory

Rows follow reading order. The note numbers are the displayed numbers. In the frozen HTML, displayed notes 18–24 have IDs `sn19`, `sn20`, `sn21`, `sn22`, `sn23`, `sn24`, `sn18`. Note 9 gives figure provenance and contains no literature citation. The “In essay” column records identifiers actually supplied, and the next column supplies the DOI or a fallback. **CR** means a matching Crossref work record was retrieved by DOI, **DC** means a matching DataCite record, and **archive** means an institutional record, primary copy or publisher catalogue was consulted. Registry matches establish the bibliographic identity. Browser access to some DOI landing pages or full texts was restricted. The three identifiers printed as DOIs in note 22 all match their cited works. The last column records additional claim checks and their limits.

| Note | Authors | Title | Venue or publisher | Year | Pages / locator | In essay | Identifier to use | Verification status |
|---|---|---|---|---|---|---|---|---|
| 1 | A. K. Wright, M. Felleisen | A syntactic approach to type soundness | Information and Computation 115(1) | 1994 | 38–94 | — | [DOI](https://doi.org/10.1006/inco.1994.1093) | CR. Publisher abstract describes the syntactic method and subject reduction. |
| 1 | R. Milner | A theory of type polymorphism in programming | Journal of Computer and System Sciences 17(3) | 1978 | 348–375 | — | [DOI](https://doi.org/10.1016/0022-0000(78)90014-4) | CR. |
| 1 | R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer | RustBelt: Securing the foundations of the Rust programming language | Proceedings of the ACM on Programming Languages 2(POPL) | 2018 issue | Art. 66, 34 pp. | — | [DOI](https://doi.org/10.1145/3158154) | CR. Online December 2017, assigned to POPL 2018. Retain 2018 for the issue citation. |
| 2, 13 | W. W. Tait | Intensional interpretations of functionals of finite type I | Journal of Symbolic Logic 32(2) | 1967 | 198–212 | — | [DOI](https://doi.org/10.2307/2271658) | CR. Note 13’s exact head-expansion condition still needs a pinpoint. |
| 2 | G. D. Plotkin | Lambda-definability and logical relations | University of Edinburgh, memorandum SAI-RM-4 | 1973 | — | — | Edinburgh author-hosted scan, identifiable by report number | Primary scan metadata matched. Crossref search found no matching DOI. Add the stable author-hosted report link. |
| 2 | R. Statman | Logical relations and the typed λ-calculus | Information and Control 65(2–3) | 1985 | 85–97 | — | [DOI](https://doi.org/10.1016/S0019-9958(85)80001-2) | CR. |
| 3 | M. Schönfinkel | Über die Bausteine der mathematischen Logik | Mathematische Annalen 92(3–4) | 1924 | 305–316 | — | [DOI](https://doi.org/10.1007/BF01448013) | CR. |
| 3 | H. B. Curry, R. Feys, with two sections by W. Craig | Combinatory Logic, vol. I | North-Holland | 1958 | — | — | [1958 edition catalogue](https://openlibrary.org/books/OL215745M) | Catalogue. No matching DOI found for this edition. The title-page credit for Craig is optional bibliographic detail. |
| 4, 10 | J. H. Morris | Lambda Calculus Models of Programming Languages | MIT PhD thesis, archived as MIT-LCS-TR-057 | 1968 | — | — | [MIT handle](https://hdl.handle.net/1721.1/149376) | Archive. Verify the exact observation predicate before retaining “only whether a run ends.” |
| 5 | J.-M. Andreoli | Logic programming with focusing proofs in linear logic | Journal of Logic and Computation 2(3) | 1992 | 297–347 | — | [DOI](https://doi.org/10.1093/logcom/2.3.297) | CR. |
| 5 | P. B. Levy | Call-by-Push-Value: A Functional/Imperative Synthesis | Springer / Kluwer | 2003 | — | — | [DOI](https://doi.org/10.1007/978-94-007-0954-6) | CR and publisher. Add the subtitle. |
| 5 | N. Zeilberger | The Logical Basis of Evaluation Order and Pattern-Matching | Carnegie Mellon PhD thesis, CMU-CS-09-122 | 2009 | — | — | [CMU report catalogue](https://www.cs.cmu.edu/~./reports/) · CMU-CS-09-122 | Title page matched. No matching DOI found. Link a repository copy or cite the report number. |
| 5 | A. Abel, B. Pientka, D. Thibodeau, A. Setzer | Copatterns: Programming infinite structures by observations | POPL | 2013 | 27–38 | — | [DOI](https://doi.org/10.1145/2429069.2429075) | CR. Use paper DOI, since another ACM DOI also indexes the proceedings entry. |
| 6 | G. D. Plotkin | A structural approach to operational semantics | Aarhus University, DAIMI FN-19 | 1981 | — | — | [2004 reprint DOI](https://doi.org/10.1016/j.jlap.2004.05.001) | CR for the Journal of Logic and Algebraic Programming reprint, vols. 60–61, pp. 17–139. Label the reprint if using its DOI. |
| 6 | G. Kahn | Natural semantics | STACS 87, LNCS 247, Springer | 1987 | 22–39 | — | [DOI](https://doi.org/10.1007/BFb0039592) | CR. |
| 7, 22 | G. Huet, J.-J. Lévy | Computations in Orthogonal Rewriting Systems, I | Computational Logic: Essays in Honor of Alan Robinson, eds. J.-L. Lassez and G. D. Plotkin, MIT Press | 1991 | 395–414 | — | [Host book](https://mitpress.mit.edu/9780262121569/computational-logic/), ISBN 9780262121569 | Archive / primary text, Part I §3 and Theorem 3.26. No matching chapter DOI found. Use “G. D. Plotkin” in the editor credit. |
| 7, 22 (via 7) | G. Huet, J.-J. Lévy | Computations in Orthogonal Rewriting Systems, II | Same MIT Press volume | 1991 | 415–443 | — | [Host book](https://mitpress.mit.edu/9780262121569/computational-logic/), ISBN 9780262121569 | Archive. Give separate chapter ranges if citing both. Part I is the direct source for the normal-derivation theorem and residual construction. |
| 8 | D. S. Scott, C. Strachey | Toward a Mathematical Semantics for Computer Languages | Oxford University Computing Laboratory, PRG-6 | 1971 | Abstract and introduction | — | [Oxford report](https://www.cs.ox.ac.uk/files/3228/PRG06.pdf) | Archive / primary text. Assignment of abstract meanings supported. The operational-normal-form claim needs C4. |
| 10 | G. D. Plotkin | LCF considered as a programming language | Theoretical Computer Science 5(3) | 1977 | 223–255 | — | [DOI](https://doi.org/10.1016/0304-3975(77)90044-5) | CR. |
| 11 | H. P. Barendregt | The Lambda Calculus: Its Syntax and Semantics, revised ed. | North-Holland | 1984 | — | — | ISBN 9780444867483 | Catalogue. DOI for the cited revised edition unconfirmed. |
| 11 | C. B. Jay, N. Ghani | The virtues of eta-expansion | Journal of Functional Programming 5(2) | 1995 | 135–154 | — | [DOI](https://doi.org/10.1017/S0956796800001301) | CR. |
| 12 | T. Altenkirch, P. Dybjer, M. Hofmann, P. Scott | Normalization by evaluation for typed lambda calculus with coproducts | LICS | 2001 | 303–310 | — | [DOI](https://doi.org/10.1109/LICS.2001.932506) | CR. The paper concerns normalization with coproducts in its specified calculus. |
| 13 | J.-Y. Girard, Y. Lafont, P. Taylor | Proofs and Types | Cambridge University Press, Cambridge Tracts in Theoretical Computer Science 7 | 1989 | Chs. 6, 14 | — | ISBN 9780521371810 | Catalogue / primary text. Ch. 14 gives the candidate conditions for the polymorphic calculus. |
| 13 | A. M. Pitts | Parametric polymorphism and operational equivalence | Mathematical Structures in Computer Science 10(3) | 2000 | 321–359 | — | [DOI](https://doi.org/10.1017/S0960129500003066) | CR. |
| 13 | J. Vouillon, P.-A. Melliès | Semantic types: A fresh look at the ideal model for types | POPL | 2004 | 52–63 | — | [DOI](https://doi.org/10.1145/964001.964006) | CR. This is the DOI left pending in the repository’s literature notes. |
| 14 | P. Freyd, G. M. Kelly | Categories of continuous functors, I | Journal of Pure and Applied Algebra 2(3) | 1972 | 169–191 | — | [DOI](https://doi.org/10.1016/0022-4049(72)90001-1) | CR. State the application to representables as in C7. |
| 14 | C. Cassidy, M. Hébert, G. M. Kelly | Reflective subcategories, localizations and factorization systems | Journal of the Australian Mathematical Society, Series A 38(3) | 1985 | 287–329 | — | [DOI](https://doi.org/10.1017/S1446788700023624) | CR. The publisher’s online record has a stray “a” in “factorizationa.” Retain the essay’s spelling. |
| 15, 20 | P. van Emde Boas | Machine models and simulations | Handbook of Theoretical Computer Science, vol. A, ed. J. van Leeuwen, Elsevier | 1990 | 1–66 | — | [DOI](https://doi.org/10.1016/B978-0-444-88071-0.50006-0) | CR. The chapter gives machine simulations and distinguishes polynomial robustness as a thesis about reasonable models. |
| 15 | B. Accattoli, U. Dal Lago | (Leftmost-outermost) beta reduction is invariant, indeed | Logical Methods in Computer Science 12(1) | 2016 | Art. 4 | — | [DOI](https://doi.org/10.2168/LMCS-12(1:4)2016) | CR / publisher. Leftmost-outermost β-reduction, as in C8. |
| 16, 20 (via 16) | S. Mac Lane | Natural associativity and commutativity | Rice University Studies 49(4) | 1963 | 28–46 | — | [Rice handle](https://hdl.handle.net/1911/62865) | Archive. Original associativity coherence source. |
| 16, 20 (via 16) | M. L. Laplaza | Coherence for associativity not an isomorphism | Journal of Pure and Applied Algebra 2(2) | 1972 | 107–120 | — | [DOI](https://doi.org/10.1016/0022-4049(72)90016-3) | CR. |
| 16, 20 (via 16), 22 | C. C. Squier, F. Otto, Y. Kobayashi | A finiteness condition for rewriting systems | Theoretical Computer Science 131(2) | 1994 | 271–294 | — | [DOI](https://doi.org/10.1016/0304-3975(94)90175-9) | CR / publisher abstract. Scope is finite derivation type for monoid presentations. Theorems 5.2–5.3 are identified by the later [Guiraud–Malbos restatement](https://arxiv.org/abs/1402.2587), Theorems 4.3.2–4.3.3. The original full text was unavailable. |
| 17 | B. Jay | Reflective Programs in Tree Calculus | Author-distributed book | 2021 | — | — | [Official specification and its book link](https://treecalcul.us/specification/) | Archive by reference. The site distinguishes the book’s original rules from the five-rule presentation. No matching book DOI or ISBN confirmed. |
| 17, 19 | B. Jay, J. Vergara | Confusion in the Church–Turing Thesis | arXiv preprint | 2014 first posted | — | arXiv:1410.7103 | [DOI](https://doi.org/10.48550/arXiv.1410.7103) | DC / primary preprint. Encoding and equivalence definitions are the relevant passage. Pin the revision used. |
| 17 | Tree Calculus website | Specification | treecalcul.us | undated | Small-step rules and “Conventions” | Described in prose | [Specification](https://treecalcul.us/specification/) | Primary specification. Rules (3a)–(3c) inspect the three shapes. |
| 18 | A. Church | An unsolvable problem of elementary number theory | American Journal of Mathematics 58(2) | 1936 | 345–363, §7 | — | [DOI](https://doi.org/10.2307/2371045) | CR / JSTOR. §7 distinguishes the effective-calculability proposal from formal results. |
| 18 | S. C. Kleene | λ-definability and recursiveness | Duke Mathematical Journal 2(2) | 1936 | 340–353 | — | [DOI](https://doi.org/10.1215/S0012-7094-36-00227-2) | CR. Direct source for the λ-definability/recursiveness comparison used by Turing’s 1937 JSL opening. |
| 18 | A. M. Turing | On computable numbers, with an application to the Entscheidungsproblem | Proceedings of the London Mathematical Society s2-42(1) | 1937 issue | 230–265 | — | [DOI](https://doi.org/10.1112/plms/s2-42.1.230) | CR / publisher. §9 gives the human-computation argument. The appendix addresses the λ comparison. The separate JSL paper is more direct. |
| 18 | A. M. Turing | Computability and λ-definability | Journal of Symbolic Logic 2(4) | 1937 | 153–163 | — | [DOI](https://doi.org/10.2307/2268280) | CR / publisher extract. Opening, p. 153, states both directions and explains the reliance on the prior recursiveness result. |
| 19 | U. Boker, N. Dershowitz | Comparing computational power | Logic Journal of the IGPL 14(5) | 2006 | **633–647** | — | [DOI](https://doi.org/10.1093/jigpal/jzl003) | CR and OUP agree on 647. Change 648 to 647. The abstract explains why representation can affect comparisons. |
| 19 | M. Felleisen | On the expressive power of programming languages | Science of Computer Programming 17(1–3) | 1991 | 35–75 | — | [DOI](https://doi.org/10.1016/0167-6423(91)90036-W) | CR. |
| 20 | C. Slot, P. van Emde Boas | On tape versus core: An application of space efficient perfect hash functions to the invariance of space | STOC | 1984 | 391–400 | — | [DOI](https://doi.org/10.1145/800057.808705) | CR. Complete the title. This paper’s title puts the emphasis on space invariance. Cite van Emde Boas’s chapter for the time-overhead thesis. |
| 20 | J. Longley, D. Normann | Higher-Order Computability | Springer | 2015 | — | — | [DOI](https://doi.org/10.1007/978-3-662-47992-6) | CR. Add a chapter or separation example for the specific card claim. |
| 20 | R. De Nicola, M. C. B. Hennessy | Testing equivalences for processes | Theoretical Computer Science 34(1–2) | 1984 | 83–133 | — | [DOI](https://doi.org/10.1016/0304-3975(84)90113-0) | CR. |
| 20 | R. Milner | Communication and Concurrency | Prentice Hall | 1989 | — | — | ISBN 0-13-115007-3 | Institutional publication catalogue. No matching DOI found. |
| 20 | R. J. van Glabbeek | The Linear Time – Branching Time Spectrum I: The Semantics of Concrete, Sequential Processes | Handbook of Process Algebra, eds. J. A. Bergstra, A. Ponse, S. A. Smolka, Elsevier | 2001 | 3–99 | — | [DOI](https://doi.org/10.1016/B978-044482830-9/50019-9) | CR. Complete the title. |
| 20 | A. Joyal, M. Nielsen, G. Winskel | Bisimulation from open maps | Information and Computation 127(2) | 1996 | 164–185 | — | [DOI](https://doi.org/10.1006/inco.1996.0057) | CR. Path lifting in the definition of openness, with a span of open maps defining the induced bisimilarity. Compare the transition-system instance. Exact journal-page locator unconfirmed. |
| 20 | M. Hofmann, T. Streicher | The groupoid interpretation of type theory | Twenty Five Years of Constructive Type Theory, Oxford University Press | 1998 | **83–112** per OUP | — | [DOI](https://doi.org/10.1093/oso/9780198501275.003.0008) | CR and publisher. The essay’s 83–111 also occurs in bibliographies. Use 83–112 for OUP’s DOI-linked version. |
| 20 | M. R. Bridson | The geometry of the word problem | Invitations to Geometry and Topology, eds. M. R. Bridson and S. M. Salamon, Oxford University Press | 2002 | 29–91 | — | [DOI](https://doi.org/10.1093/oso/9780198507727.003.0002) | CR. General area and word problem reference. Supply the independent grid argument in C13. |
| 20 | P. S. Novikov | On the algorithmic unsolvability of the word problem in group theory | Trudy Matematicheskogo Instituta imeni V. A. Steklova 44 | 1955 | 3–143 | — | [Math-Net entry](https://www.mathnet.ru/eng/tm1180) | Archive. Full title, venue and pages replace the author–year mention. |
| 20 | W. W. Boone | The word problem | Annals of Mathematics 70(2) | 1959 | 207–265 | — | [DOI](https://doi.org/10.2307/1970103) | CR / journal issue. |
| 21 | F. W. Lawvere | Metric spaces, generalized logic, and closed categories | Rendiconti del Seminario Matematico e Fisico di Milano 43(1) | 1973 | 135–166 | — | [DOI](https://doi.org/10.1007/BF02924844) | CR. The [2002 reprint](https://www.tac.mta.ca/tac/reprints/articles/1/tr1abs.html) has its own pagination. |
| 22 | Terese | Term Rewriting Systems | Cambridge University Press | 2003 | Ch. 8, especially §§8.1.4, 8.1.8, 8.3.2 | — | ISBN 0-521-39115-6, [publisher front matter](https://assets.cambridge.org/052139/1156/sample/0521391156WS.pdf) | Archive. Chapter and section titles verified. Crossref search locates reviews with separate DOIs. |
| 22 | V. van Oostrom, R. de Vrijer | Four equivalent equivalences of reductions | Electronic Notes in Theoretical Computer Science 70(6) | 2002 | 21–61 | 10.1016/S1571-0661(04)80599-1 | [DOI](https://doi.org/10.1016/S1571-0661(04)80599-1) | CR and primary text. §3 gives the permutation equations, Theorem 7.1 gives the four-way comparison, and Remark 7.6(i) qualifies the labelling correspondence for collapsing rules. |
| 22 | Y. Lafont | Interaction nets | POPL | 1990 | 95–108, Proposition 1 | 10.1145/96709.96718 | [DOI](https://doi.org/10.1145/96709.96718) | CR and primary text. Proposition 1 gives the strong-confluence result. |
| 22 | Y. Lafont | Interaction combinators | Information and Computation 137(1) | 1997 | 69–101, Proposition 1, pp. 73–74 | 10.1006/inco.1997.2643 | [DOI](https://doi.org/10.1006/inco.1997.2643) | CR and primary text. The paragraph after Proposition 1 gives the fixed length to an irreducible net. |
| 23 | The Univalent Foundations Program | Homotopy Type Theory: Univalent Foundations of Mathematics | Institute for Advanced Study | 2013 | §8.1 | — | [Official book site](https://homotopytypetheory.org/book/) | Archive. Section on the fundamental group of the circle contains the integer family with successor transport. |
| 24 | B. P. Hilken | Towards a proof theory of rewriting: The simply typed 2λ-calculus | Theoretical Computer Science 170(1–2) | 1996 | 407–444 | — | [Publisher DOI](https://doi.org/10.1016/S0304-3975(96)80713-4) | CR and publisher abstract for the directed typed rewriting system. [The alternate DOI in the repository notes](https://doi.org/10.1016/S0304-3975(96)00097-7) has a second Crossref record for the same article. Use the DOI printed on the publisher page. The [1994 report](https://doi.org/10.48456/tr-336) is a separately identified version. |
| 24 | M. Fiore, P. Saville | Coherence and normalisation-by-evaluation for bicategorical cartesian closed structure | LICS | 2020 | 425–439, Theorem 1.1 | — | [DOI](https://doi.org/10.1145/3373718.3394769) | CR and primary text. The 2021 journal paper’s DOI is a different record. Use the 2020 proceedings DOI here. |
| 24 | J. C. Baez, C. Williams | Enriched Lawvere theories for operational semantics | Electronic Proceedings in Theoretical Computer Science 323 | 2020 | 106–135, §§5, 5.2 | — | [DOI](https://doi.org/10.4204/EPTCS.323.8) | CR and [primary manuscript](https://arxiv.org/abs/1905.05636). Sections 5 and 5.2 give change of base and the operational-to-denotational example. |
