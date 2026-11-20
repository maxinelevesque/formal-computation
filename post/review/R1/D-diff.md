# R1 D · Diff check

Reviewed `60a2b0d..c131cae` for the essay. The main blockers are the scope of code-reading with open trees, the distinction between a result-port reading and a completed net run, and claims about loops that exceed the displayed traces or the linked proofs.

`python3 -I scripts/lean-links.py 1e18e37 --check` exited 0 and printed:

```text
183 declaration links at 1e18e37d6842; 0 problems
```

All nine distinct tree-semantics declaration targets were present at their linked lines at `5147cfa`. Running the essay’s embedded reducer under Node reproduced the 24 tree/net bench reading pairs, the three-interaction readbacks for `K u v` and `K a (ω ω)`, and the ten-interaction normal net for `K a (I b)`. The latter’s reachable graph was exhausted below the browser’s cap, with 44 states and one normal state. The outermost `ω ω` run had 1,001 distinct browser state keys through 1,000 interactions. These checks used the browser model’s state keys and readback, and were independent of Lean. For DOI metadata I checked the changed references against the C-pass inventory and consulted the primary sources for the substantive changes. Direct Crossref requests for the Jay–Ghani and Fiore–Saville DOIs failed in this session. Their publisher and proceedings records confirm the identifiers. [Jay–Ghani](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/FAAA27786A519A85C8DFB650AC8864AD/S0956796800001301a.pdf/the-virtues-of-eta-expansion.pdf) · [Fiore–Saville](https://www.research.ed.ac.uk/en/publications/coherence-and-normalisation-by-evaluation-for-bicategorical-carte/)

## Findings

### D1. Tree triage cannot read all open normal forms

- **Location** — Calculus switch, “Every tree is a leaf, a stem △ u or a fork △ u v.” When probes can read atoms, “In tree calculus a program can ask of any normal form whether it is a leaf, a stem or a fork, and take it apart accordingly” and “the tree calculus’s own probes, which read only variables, give sameness after running on every term with a value”.
- **Problem** — The specification’s three shapes classify closed values. The essay’s open calculus has normal forms such as bare variables and applications headed by a variable. Take two different free variables `a` and `b`. They are different normal forms and confluence puts them in different fibres. Any common fresh probe is unchanged by swapping `a` and `b`. Reduction commutes with that swap and every allowed reading is fixed by it, so the probe cannot distinguish them. `Tree.exists_eq` compares closed trees in strict evaluation. `Calculus.codeEq_iff_conv` uses a different observation that reads any normal form directly. Neither supports the open triage characterization. The code-reading card and the hand-argued list repeat or inherit the overstatement. [Tree-calculus specification](https://treecalcul.us/specification/)
- **Severity** — block
- **Suggested fix** — Scope the shape classification and intrinsic triage characterization to closed values, give the recursive shape-test argument in that scope, and carry the qualification into the figure, card and status list. Keep direct normal-form readback as a separate observation. The fixed-shape probe for ‘Runs to I’ can still be argued for open inputs, since only the matches reaching the closed shape of `I` need to succeed.

### D2. The displayed type test uses a fixed variable

- **Location** — Types, “‘Returns a when applied to a’ is defined by a probe, and its shading is drawn in blue.”
- **Problem** — The figure uses the fixed application `[ ] a` and tests whether the result is `a` (`returnsA`). The newly stated freshness rule excludes this as a probe on terms already containing `a`. For example, `K a` under `[ ] a` yields `a`, but a fresh `[ ] x` cannot read the result supplied by `K a`. `SKI.isType_probePred` and `SKI.probePred_respects` use the more permissive `Reads` of `SKI/Probes.lean`. The new general paragraph at the end of the cards likewise mixes that formal observation with the fresh one.
- **Severity** — block
- **Suggested fix** — Describe the blue shading and its Lean marks as the fixed-variable predicate in the formal model, or change the example to a genuinely fresh application test and give the corresponding argument. Use the same scope in the table and in the observation recap.

### D3. Generic probe theorems have a specific notion of calculus

- **Location** — Changing the ingredients, “Reading only what was supplied keeps probes coarser than running, since a probe that may read every normal form it reaches makes sameness under probes into sameness after running on terms that have a value.” Mechanized, “In any calculus whose steps can be taken inside a probe, sameness under probes is kept by every context”. Footer, “in any calculus with probes”.
- **Problem** — `Calculus.codeEq_iff_conv` assumes confluence and a readback from one side, and compares full-normal-form `CodeEq` with conversion. It cannot establish the claimed strict gap for the fresh observation. The implication from conversion to restricted probe equivalence uses confluence plus the context laws and normality of readable outcomes, or follows directly from already established reading invariance. `Calculus.probeEq_plug` uses context composition with the substitution law, not step compatibility alone. The essay’s broad definition of an observer includes costs and traces and does not impose these laws. `Obs.Pairing` also has a propositional `pass` field, whereas the essay allows richer verdicts.
- **Severity** — block
- **Suggested fix** — Attach each mark to its precise implication. Give the assumptions of `Calculus` in the generic rows and limit the footer to the particular model of probes. Cite the three SKI identities for strictness in that calculus. Specify the yes/no verdict in the `Obs.Pairing` row.

### D4. One-step diamonds and the open-net implementation

- **Location** — Atoms and probes and Mechanized, “two different interactions lead to a common net in one more interaction each.” Atoms and probes, “That the count does not depend on the order of interactions follows from a general theorem.”
- **Problem** — `Ix.strong_confluence` gives equal immediate reducts **or** a one-step join, with `WF`, table well-formedness and determinism. `Diamond.equal_lengths` uses the diamond for *distinct reducts*. `Ix.fire_commute` is a separate result about firing two applicable well-formed rules on disjoint active pairs of a well-formed net. The paragraph starts with counts from an open JavaScript reducer and then presents their order-independence as a theorem without establishing that the JavaScript states and steps satisfy the hypotheses. Mechanized separates those computations from the formal results. The same formal/browser transition occurs under the running and fibre figures.
- **Severity** — block
- **Suggested fix** — State the equal-reduct alternative in the theorem sentences. Put well-formedness on the disjoint-pair statement where it is repeated, and attach order-independence to completed runs of the formal relation. If asserting it about the displayed nets, supply an argument for the browser model or report the finite exploration as browser evidence. [Lafont, Proposition 1 and its consequence](https://www.sciencedirect.com/science/article/pii/S0890540197926432/pdf)

### D5. The strict compilation result and the shared source for run comparisons

- **Location** — Calculus switch and Mechanized, “the compiled net finishes and reads back that value”. Mechanized, “runs that finish have the same length” and “fire the same interactions in different orders”.
- **Problem** — `Ix.TC.eager_sound` starts with a particular `Tree.Eval f x v` and produces one finite normal run with output and readback `v`. Its statement alone does not quantify over all reduction orders. `Ix.Steps.equal_lengths` and `Ix.Event.Run.perm` compare runs from the **same** starting net to normal endpoints. The latter gives a permutation of canonical agent-pair labels, allowing identical order.
- **Severity** — should
- **Suggested fix** — Say “has a run to a normal net that reads back that value”. If claiming every order, cite and apply the separate termination and uniqueness results with their hypotheses. In the list and fibre note, state “from the same starting net” and “the same interaction labels, possibly in a different order”.

### D6. Reading a result port is earlier than finishing a net

- **Location** — Changing the ingredients, net length readout, “On the left every run to a has the same length, ten interactions as the browser counts them, whatever the order.”
- **Problem** — `a` is already the readback after interaction 3 in the outermost browser run of `K a (I b)`. Interaction 10 reaches the irreducible net. This contradicts the preceding running section’s correct distinction between readback and completion. The marked length theorem requires normal endpoints and says nothing about the first time a port reads a particular answer.
- **Severity** — block
- **Suggested fix** — Say that the browser’s runs to the **final irreducible net** have length ten. Keep the result-port observation, if used here, distinct from that count.

### D7. Bounded net observations are presented as unbounded conclusions

- **Location** — Running a term, “The loop ω ω is left out, because its eager net grows.” What a type cannot see, “In the run shown the reading stays a and the interactions do not stop.” Changing the ingredients, net fibre readout, “the hollow point that stands for no value”.
- **Problem** — The exit panel builds a trace capped at 400 interactions and loops the animation. The other panel explores to depth five, and the cited experiment checks 1,000 outermost interactions. These support continuing work within the checked prefix and no repeated state within that bound. They do not prove unbounded growth, divergence, or that no order yields a value in the eager browser model. The linked lazy example proves a different result for a closed compilation and the strict non-evaluation of the source term.
- **Severity** — block
- **Suggested fix** — In prose, live readouts and accessible descriptions, say that the eager trace is still active at the cap and which readings were observed. Label the right-hand point “no value reached in the view” unless supplying a separate argument for the eager net. Identify the strategy and bound wherever they do the work.

### D8. A drawn tree cycle does not establish a hole

- **Location** — Changing the ingredients, tree fibre accessible label, “a ring with a hole that a round trip cannot shrink past”. What a type cannot see, “It has no exit, and no order of evaluation gives it a value.”
- **Problem** — `Tree.omega_cycle` supplies a five-step path returning to its start. It makes no assertion about the localization, other reductions or normalization. The tree figure’s live readout also concludes “nothing fills the loop of five terms” and “no route reaches a value at any length”. The SKI cycle in the second quote does have outgoing reductions outside the chosen cycle. For example the embedded SKI reducer finds `ω (I ω)` from `I ω (I ω)`, outside the selected cycle. The Running section already acknowledges these steps. A cycle alone does not rule out reaching a normal form.
- **Severity** — block
- **Suggested fix** — Say which cycle the figure follows. In the tree case report a hole in the displayed graph before any outside edges or run equations are considered, or supply a proof for the full fibre and record its status. For the SKI sentence, distinguish exits from the displayed cycle from paths to a normal form, and give an argument or reference for the latter’s absence.

### D9. The full SKI hole is conditional in the supporting argument

- **Location** — Changing the ingredients, “That nothing fills it once every step can be taken back has been argued by hand from the count on terms without K, and only the count is mechanized.”
- **Problem** — `SKI.wt_permEq` is a K-free invariant, and `SKI.not_absorbed'` proves that no forward continuation absorbs the displayed lap under the mechanized equations. A zigzag in the full localization can pass backwards into terms containing K. The hand argument in `notes/04-examples.md`, “Full SKI”, assumes that the run quotient matches Lévy’s and admits the relevant calculus of fractions. Mechanized expressly lists the equality of the two quotients as open.
- **Severity** — block
- **Suggested fix** — State survival in the K-free localization and the proved non-absorption under forward continuation separately. Make survival in the full SKI localization conditional on the fraction argument, in both the body and “Argued by hand”, or supply the missing argument for the actual quotient.

### D10. A bounded calculator does not derive every point or arrow

- **Location** — Three equalities, “On the fourteen terms of the figure, as the browser computes them, it then puts the points where sameness after running does.” Mechanized, “A small reducer in the page computes every arrow in the large figures, every reading in the tables of probes in all three calculi, and the points on the line.” Footer, “their grouping into fibres were made by hand.”
- **Problem** — The alternate bundle has nineteen terms. In the tree/net equality figure the probe partition is displayed using the stored running-fibre groups, with the three identity points kept apart. The bench tests the identities and six closed terms, and does not exhaust contexts or establish that partition for the nineteen terms. Some figures, including the bracketings diagram and SKI/tree fibre panels, use explicit edge lists or hand-drawn arrows. The reducer does compute the bench readings, induced bundle edges and bounded net graphs. Its result-port readback also has failure and truncation cases, so “reads every net back” is broader than the implementation.
- **Severity** — block
- **Suggested fix** — Label the bench point numbers and the computed edges and net graphs as computed. Describe the equality figure’s grouping as supplied, or give separating probes for the full set of displayed classes under the stated observation. Name the 19-term bundle in tree/net mode, and give the scope of result-port readback.

### D11. The time bound needs input size and the normalization endpoint

- **Location** — What a type cannot see, “for the λ-calculus, Accattoli and Dal Lago prove that counting leftmost-outermost β-steps measures time on a machine to within a polynomial.”
- **Problem** — The invariance result concerns leftmost-outermost derivations to normal form. The simulation time is polynomial in the initial term’s size **and** the length of the derivation, with a shared representation of the normal form. Derivation length alone cannot bound the time to read an arbitrarily large input. The paper’s size-explosion point also rules out reading this as a promise to print expanded normal forms within that bound.
- **Severity** — block
- **Suggested fix** — State the two parameters and the normalization endpoint, and name the shared representation if mentioning the machine’s output. [Accattoli–Dal Lago](https://arxiv.org/abs/1601.01233)

### D12. Effective local steps do not specify a partial function

- **Location** — Changing the ingredients, “A calculus with finite descriptions and finitely many local rules, in which numbers are written and read by effective rules, can be run by a Turing machine, and so adds no point.” First card, “Every universal calculus whose rules a Turing machine can carry out has the same line, the partial recursive functions.”
- **Problem** — The premises fail to specify an effective way to generate or choose a next step, or a single-valued convention for successful outcomes. Even two ordinary local rules rewriting the same initial symbol to different numerals can give two answers on one input. The cited Church/Kleene/Turing results compare specific formal models. They do not supply operational hypotheses for every calculus. Also, the preceding paragraph sets descriptions to configurations but puts *programs* on the observation line. A probe supplying an input runs a program from a configuration constructed with that input.
- **Severity** — block
- **Suggested fix** — Say that the comparison regards programs as the observed objects and configurations as their states. State a sufficient condition for simulation, such as effective encoding, a fixed effective strategy, effective halting and readout, and a single-valued numerical outcome convention. Use that formulation in the card and Summary. [Turing, Computability and λ-definability](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/computability-and-definability/FE8B4FC84276D7BACB8433BD578C6BFD)

### D13. Keeping fibres can still identify runs

- **Location** — Summary, “Keeping the fibres distinguishes runs that end at the same value.”
- **Problem** — The essay’s own `K a (I b)` example identifies two distinct routes to `a`. In the SKI normal-form fibres with Lévy’s equivalence, the normal derivation theorem identifies all routes from a term to its value. The summary’s unconditional sentence contradicts those examples.
- **Severity** — block
- **Suggested fix** — Say that keeping the fibres can distinguish routes to the same value when the selected equations leave them distinct. [Huet–Lévy, Theorem 3.26](https://www.cs.tufts.edu/comp/150FP/archive/gerard-huet/orthogonal-rewriting.pdf)

### D14. Conversion and equality propositions

- **Location** — Three equalities, “An equality decided by running in this way is what a proof assistant calls definitional.” Also “an equality that needs a proof is called propositional” and “Lean’s definitional equality includes η for functions and for types with a single constructor”.
- **Problem** — The reduction example illustrates conversion, but Lean also has η and proof irrelevance in its definitional equality. Propositional equality is the equality type and can also be inhabited by reflexivity when two terms are definitionally equal. Lean’s structure η requires more than a single constructor. The implementation’s structure condition excludes recursive or indexed cases. The article on coproduct normalization concerns a specific calculus and does not establish the general claim that such laws are hard to use as steps in all systems.
- **Severity** — should
- **Suggested fix** — Call the running example one source of definitional equality. Define propositional equality as an equality proposition, with induction needed for the particular open addition example. Say “functions and structures” for Lean η, and describe the coproduct citation as a particular normalization result. [Lean type system](https://lean-lang.org/doc/reference/latest/The-Type-System/) · [Lean expression reference](https://leanprover.github.io/hex/docs/Lean/Expr.html)

### D15. The opening claims equivalence where the cited results prove soundness

- **Location** — Opening, “Proofs of type soundness show that the two agree, by syntactic means or with types as predicates.” Two accounts of a typed program, “A term that can be derived therefore passes every test that its type imposes.”
- **Problem** — The formal results establish a direction from typing to safety or semantic membership. They do not establish that every term in a semantic predicate is derivable at that type. For the fundamental lemma under assumptions Γ, the semantic conclusion requires an environment or substitution satisfying Γ. The unqualified last sentence leaves this out.
- **Severity** — should
- **Suggested fix** — Use the direction from typing to safe or semantically well-typed behavior, and qualify the fundamental lemma with a closing substitution satisfying the assumptions, or state the empty-context consequence. [Milner, §3](https://www.sciencedirect.com/science/article/pii/0022000078900144)

### D16. Proofs of reachability are about possible finite runs

- **Location** — Three equalities, “By confluence, the property that two runs from one term can always be continued until they meet, the two runs end alike, and the probe reads the same thing from both.”
- **Problem** — `SKI.probeEq_of_conv` compares the existence of runs to a readable outcome. Confluence joins finite reducts, and does not entail that two chosen strategies both finish. The essay’s loop with exits illustrates the difference. A probe with repeated holes also needs a run that advances every copy, rather than necessarily a single step.
- **Severity** — should
- **Suggested fix** — Say that if one experiment has a finite run to a readable normal form, the other has a run to that same form. Say “a run inside the context” in the repeated-hole case. Describe the figure’s particular strategy separately.

### D17. Predicate evidence and the comparison with reducibility candidates

- **Location** — Types, “Until the section on changing the ingredients the two coincide.” Also “such a condition excludes it while including a, which is one step away.”
- **Problem** — Behaviours already admit non-predicate evidence in the definition and the immediately following pentagon example, before Changing the ingredients. `beh_iff_of_subsingleton_co` requires subsingleton fibres, so the coincidence is about the predicate case throughout. And strong normalization is a necessary condition for membership in Girard’s candidates, not by itself a proof of membership of `a`. The comparison is valid if it is the strong-normalization **predicate** that contains `a), or if the candidate’s neutral-term rule and typing assumptions are made explicit.
- **Severity** — should
- **Suggested fix** — Describe the predicate case without a section cutoff. Say that `a` satisfies strong normalization while `K a (ω ω)` fails it, and keep the example distinct from candidate membership. [Girard, Lafont and Taylor, chapter 14](https://www.paultaylor.eu/stable/prot.pdf)

### D18. Parallel or is a separation between languages at a higher type

- **Location** — Changing the ingredients, “parallel or is not definable in Plotkin’s PCF, though it agrees with PCF on numbers”.
- **Problem** — The connective is not itself a calculus that agrees with PCF on numbers. Plotkin supplies a higher-type operation definable in the parallel extension and absent in PCF. To use it as an example of the card’s claim one must also compare the *two languages* at the numerical function type.
- **Severity** — should
- **Suggested fix** — Name PCF and PCF with parallel-or. Explain their agreement on partial computable numerical functions using numerical expressiveness of PCF and effectiveness of the extended evaluator, and cite Plotkin for the higher-type separation. [Plotkin, LCF considered as a programming language](https://doi.org/10.1016/0304-3975(77)90044-5)

### D19. Scope of the pentagon mark and the right-spine count

- **Location** — Changing the ingredients, “the pentagon of bracketings, read as a loop by going down one route and back up the other, is filled only if an equation between the two runs is added.” Mechanized, “the same count of S-steps on the rightmost branch”.
- **Problem** — `Pentagon.top_ne_bot_localized` proves the routes unequal in the particular free presentation after inverting its arrows. It does not assert that a *direct* equation is necessary in every extension. Other equations could imply it. The right-spine phrase is supported by `Step.wt`, but “rightmost branch” can be mistaken for just the branch in the starting text. The position is tested in the source of each step, with the root included.
- **Severity** — should
- **Suggested fix** — State nontriviality for the displayed presentation and that the pentagon equation fills it. Say that the counter counts steps at the root or reached from there by following argument edges, in each step’s source term.

### D20. Cite the issue date and add a locator for historical terminology

- **Location** — Atoms and probes, “PhD thesis, Massachusetts Institute of Technology, 1968, hdl:1721.1/149376”. Running a term, “Small-step and big-step presentations are due to G. D. Plotkin” and “G. Kahn”.
- **Problem** — The Morris handle targets the December 1968 technical-report edition. MIT’s thesis catalogue gives 1969, while the thesis title page records submission in 1968. Kahn and Plotkin support the respective presentations and are suitable references. The papers by themselves do not establish priority for small-step and big-step presentations generally.
- **Severity** — could
- **Suggested fix** — Cite the report by number and date, or cite the thesis catalogue and distinguish submission from issue date. Describe Plotkin’s structural operational semantics and Kahn’s natural semantics as sources for the respective presentations, without an unrestricted priority attribution. [Morris report](https://dspace.mit.edu/entities/publication/0556b242-90aa-475c-b261-296f299c1ef4) · [MIT thesis record](https://dspace.mit.edu/entities/publication/5fd0e97e-1b87-4fdb-9c35-8f17a42426f1)

### D21. The audit link predates six entries it claims to list

- **Location** — Mechanized, “each uses at most the three standard axioms of Lean’s logic, as listed for each statement in AXIOMS.md.”
- **Problem** — The linked `AXIOMS.md` at `1e18e37` omits `Obs.Pairing`, `Presentation`, `SKI.codeEq_of_conv`, `SKI.isType_runsToI`, `SKI.le_close` and `SKI.skRun`. The working-tree audit records all six from CI job 3164. The omission is in the pinned audit’s coverage.
- **Severity** — should
- **Suggested fix** — Pin the audit URL to the commit that includes the six entries, or state which revision contains the supplemental audit.

## Deletions for the author

- **Opening itinerary.** The paragraph beginning “The essay goes in this order.” was removed in full. It previewed typing by rules and tests, the interactive bench, the three equalities, types as invariant predicates, the operational definition, what types cannot see, code inspection, and the place of Turing computation. The sections remain. The early map through them is gone.
- **Types.** “This is the sense in which computation lies between atoms and probes.” The example still transports membership from `u` to `K u v`. The explicit return to the opening thesis was cut.
- **Three equalities.** “Something that only a probe could find out is now found by running.” The merger of the three identity points remains. The explicit interpretation of adding a rule as turning an observational equality into a computational one was cut.
- **Changing the ingredients, group words.** “Nothing in this picture resembles a machine.” The next sentences still give the bidirectional rules and absence of input, output and evaluation order. The sentence making the example a challenge to the machine intuition was cut.
- **Changing the ingredients, fibres over values.** “This is why types as predicates serve such calculi well, and why keeping only the line has seemed to lose nothing.” The preceding paragraph still explains what the line retains. The deleted inference explains why that perspective has been attractive.
- **Types, comparison with earlier methods.** The frozen text says that two-way closure “does the part of their work that the fundamental lemma needs.” The revision retains the fact that the example uses backward closure. It drops the explicit comparison of what the closure conditions do in the argument.
- **Changing the ingredients, cross-calculus comparison.** The sentence ending “The observation is therefore an ingredient in its own right” was removed in the Y apply commit. The encoding example survives, while its explicit inference back to the definition was cut.
- **Opening and close.** “Still in draft” and the claim that “a good part of the theory of programming languages” concerns agreement between the two accounts were removed. The footer retains the unpublished and unrefereed status. The broader claim about the field has no replacement. The separate claim that the usual notion “has been taken for the whole subject” was also dropped, in line with the C-pass objection about sourcing reception claims.
- **Net notes.** The frozen no-loop/no-hole claim, the unqualified global interaction counter, and the arbitrary-endpoint equal-length claim were withdrawn with an explanation in triage. The revision gives bounded experiments, commuting squares, a theorem for completed runs, and explicit open questions. The tree and eager-net status issues that remain are listed above.
