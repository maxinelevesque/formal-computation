# R1 D2 · Diff check

Reviewed `c131cae..b553b19` and the whole essay for consistency with the closed-instance decision. Of the 21 earlier findings, **14 are resolved, 7 partly resolved, and 0 unresolved**. The findings below give the remaining or newly introduced issues: **8 block, 2 should, 2 could**. The main blockers are conflicting definitions of observation on open terms, theorem marks that still cite the direct reading, and categorical statements in the figures about bounded or conditional results.

The requested link check exited 1:

```text
195 declaration links at e945f34c0161; 2 problems
  post/atoms-and-probes.html: 146 stored link(s) differ from the pin e945f34c0161 (re-run without --check)
  post/technical-companion.md: 0 stored link(s) differ from the pin e945f34c0161 (re-run without --check)
```

I checked all 144 essay declaration anchors (59 distinct declarations) against the locally available stored commit `9b151e6` and all 14 tree-semantics marks (9 distinct targets) against local commit `5147cfa`. The anchors land on the named declarations. The two pin problems are distinct from whether those declarations support their sentences. I did not request private tree-semantics URLs. No Lean build was run.

The two lab files change only the test comment, snapshot provenance and six hashes. At both 1200 and 400 px the only changed hashes are for load `#pred`, paint by hand `#pred`, and paint probeA `#paintread`. The read-only Node harness reported **256 checks passed, 0 failed**, including **1118/1118** snapshot matches both on load and after switching back to SKI.

## Earlier findings

| ID | Status | Evidence in the revised essay |
|---|---|---|
| D1 | Partly resolved | “Every closed normal form is a leaf, a stem △ u or a fork △ u v” and “On closed terms, one of which has a value” fix the positive claims. “With free variables it fails, since no such probe tells a from b” is false under comparison by closed instances. |
| D2 | Partly resolved | “‘Returns its argument’ is defined by the probe [ ] x with the reading x” changes the fixed variable and makes the closed cases valid. The figure still executes the direct fixed-variable test on open inputs and the prose never names that distinction. |
| D3 | Partly resolved | “If the calculus is confluent” and “whose readable outcomes take no step” qualify the generic theorem. “In Lean a yes or a no (a proposition)” fixes the pairing. The code result still omits necessary context laws at its first statement, and the SKI body and table still conflate direct and closed-instance equivalence. |
| D4 | Resolved | “Two interactions either give the same net or lead to a common net in one more interaction each” fixes the diamond statement. “The browser’s open nets are not covered by that proof” separates the evidence. The running note now includes “a well-formed net” and “well-formed rules on disjoint pairs”. |
| D5 | Partly resolved | “Has a run to an irreducible net that reads back that value” and “runs from the same net” fix existence and the common starting net. “Fire the same interactions, possibly in a different order” still omits the theorem’s restriction to canonical event labels. |
| D6 | Resolved | “Ten interactions in the graph the browser computes, whatever the order, though in the outermost order the result port reads a after three” distinguishes the normal endpoint from first readback. |
| D7 | Partly resolved | “Nothing beyond the cap has been checked” and “no value reached in the layers drawn” fix the main text and most readouts. The shared live annotation still says “never ends” in net mode. |
| D8 | Partly resolved | “It has steps out of the cycle as well, which are not drawn” and “whether the whole fibre has a hole is not settled for trees” fix the cycle argument in the body. The SKI text now acknowledges reductions out of the displayed cycle and argues nonnormalization separately. Tree labels still say “no value”, and the SKI run readout still infers no value from the chosen cycle. |
| D9 | Partly resolved | “A round trip through the whole fibre may pass backwards through terms with K” and “that assumption is open” qualify the full result in prose. The SKI fibre readout and figure still depict an unconditional hole. |
| D10 | Resolved | “The figure has nineteen tree terms” and “as given to the figure and not computed from probes” fix provenance in the body and readouts. The status list distinguishes the hand-supplied fibre grouping and readback “where its readback succeeds”. |
| D11 | Resolved | “A leftmost-outermost run to normal form” with time polynomial “in the size of the starting term and in the number of its β-steps”, and a “shared representation”, matches the cited result. |
| D12 | Resolved | “A probe runs a program from the configuration that its input fixes”; a “fixed effective strategy”, effectively detectable completion and readback “as at most one number” supply the missing simulation conditions. The card and summary now invoke machine-executable probes and the single-valued convention. |
| D13 | Resolved | “Keeping the fibres can distinguish runs that end at the same value, when the chosen equations between runs do not identify them.” |
| D14 | Resolved | “One source of what a proof assistant calls definitional equality” and “an equality type, and here it has to be proved” fix the distinction. The notes specify the Lean structure restriction and describe the coproduct result for “one typed calculus”. |
| D15 | Resolved | “Proofs of type soundness go from the first to the second” and “Under assumptions Γ the same holds once each variable is replaced by a term that passes the tests of its assumed type.” |
| D16 | Resolved | “Taking that step in each copy of t” and “if the experiment on either term has a finite run to a normal form the probe can read” state a finite reachability claim rather than a guarantee for chosen runs. |
| D17 | Resolved | “Where the evidence is a yes or a no, the two notions coincide” specifies the predicate case. The contrast with `a` is about “the condition that every run end”. |
| D18 | Resolved | “PCF and PCF extended with parallel or compute the same partial functions on numbers” compares languages, and “parallel or, a function of higher type, is definable in the second and not in the first” states the separation. |
| D19 | Resolved | “Is not filled in the presentation drawn” scopes the pentagon result. “At the root of the term or reached from the root by going only into arguments, in the term where the step is taken” specifies the counter at each source. |
| D20 | Resolved | “Submitted 1968 and issued as a Project MAC technical report in December 1968” distinguishes the edition and degree date. “For a small-step presentation” and “for a big-step presentation” drop priority claims. |
| D21 | Resolved | “As listed for each statement in AXIOMS.md” now points to an audit containing all six previously omitted entries. Three new entries are missing, as noted below. |

## Findings

### 1. The introductory definition still demonstrates the discarded strict rule

- **Location** — Atoms and probes, line 477, “The term K a gives a, which contains no constant, but the probe may not read it, because a came from the term.” Mechanized, line 930, “the reading rule for terms with variables of their own, under which a probe reads only the variables it supplied”.
- **Problem** — This presents running a fresh context directly on an open term as the essay’s rule, before giving a second and incompatible account. The immediate equivalence recap at line 478 again quantifies only over contexts. `ProbeEqCl` quantifies first over a **common** closing substitution and then over contexts and readings. Under the adopted rule `K a` is not an input to a reading. With `a := I`, for example, `[ ] x y` on its closed instance `K I` reads `y`. The hand-argued list misstates the chosen rule and obscures which alternative is hand-argued. “It can only supply another argument and try again” also narrows the permitted contexts to application spines.
- **Severity** — block
- **Suggested fix** — Give the closed-input restriction before the first reading example, and state the shared-substitution quantifier in the equivalence recap. Move the direct `K a` test into the rejected strict alternative or replace it with a worked closed instance. Identify the strict alternative in the hand-argued list and keep the adopted comparison in the Mechanized table. Say that the observer can try another context.

### 2. The main closed-instance statements cite the wrong relations or implications

- **Location** — Lines 477, 575 and 775, “two such terms are the same under probes when they are the same whatever terms without variables replace their variables”, “Terms joined by steps agree under every probe”, and “sameness under probes is kept by every context”.
- **Problem** — `SKI.probeEqCl_of_conv` says `Conv t u → ProbeEqCl t u`, so the first mark belongs to the conversion sentence, which currently cites `SKI.probeEq_of_conv` with consequent `ProbeEq t u`. The SKI context row cites `SKI.probeEq_plug` and the recap cites `Calculus.probeEq_plug`, both for the direct relation, while the recap just defined the closed-instance one. `SKI.probeEqCl_plug` proves precisely the latter claim. The `probeEqCl_iff_of_closed` mark after “the three rules agree” proves the two defined Lean relations agree, and the agreement with the stricter variant follows separately because a closed tested term supplies no variables. The generic code-readback result at line 693 requires a hole context with `plug_hole` as well as the lifting of steps and confluence. Generic context preservation needs composition with `plug_subst`, not just the availability of a second context. The line 890 link to `probeEqCl_subst` has no corresponding claim in that row.
- **Severity** — block
- **Suggested fix** — Attach the definition `SKI.ProbeEqCl` to the quantifier sentence, and use `probeEqCl_of_conv` and `probeEqCl_plug` for the corresponding SKI assertions in the body and table. Add substitution stability to the row if retaining that mark. State why the fresh rule agrees on closed tested inputs. Identify the generic claims as results for `Calculus` with the appropriate context laws and direct reading. `S K y` remains equivalent to `I` under closing substitutions by instantiating `SKI.probeEq_SK` at each substituted `y`. Make that argument explicit where the old mark is retained for the open claim.

### 3. The tree code-reading note asserts the opposite of closed-instance comparison

- **Location** — When probes can read atoms, line 690, “With free variables it fails, since no such probe tells a from b, which lie in different fibres.” Mechanized, line 930, “and that with free variables they cannot tell a from b”.
- **Problem** — These statements concern the rejected direct fresh-variable rule. For the closed-instance rule take a single substitution with `a := I` and `b := K`. The probe `[ ] x y` reads `x y` from the former and `x` from the latter. The tree note in Three equalities already uses a closed instance to separate the fibre of `a` from the loop. That separation can be justified even without a nonnormalization proof: the fixed closed loop cannot agree with both `I` and `K`, which the bench separates. The same section switches from intrinsic tree triage to direct normal-form readback via the SKI checkbox. The latter is the `CodeEq` experiment, which reads open normal forms directly (see `codeEq_Ia_a` and the `I a` example). The body and the script’s `coderead` use the same equality name for these different scopes.
- **Severity** — block
- **Suggested fix** — Give the closing-substitution witness for `a` and `b`, or explicitly label the old counterexample as about the rejected direct rule. State the two-instance argument for the tree loop separation. Describe SKI full readback as an alternate observation with its own policy on open inputs, and carry the distinction into the code figure and status list.

### 4. The blue predicate still reads open subjects directly

- **Location** — Types, line 601, “‘Returns its argument’ is defined by the probe [ ] x with the reading x”; script lines 3548–3549, “This predicate is defined by the probe [ ] x with the reading x.”
- **Problem** — `returnsA` applies the fixed `x` directly to every term in the bundle, including `K I a`, which it shades. The net mode uses the tree bundle and the tree reducer for this figure. `isType_probePred` and `probePred_respects` are about direct `ProbePred` and `ProbeEq`, respectively, and prove no closing-substitution implementation. The current bundle happens to agree with the universal closed-instance test: terms reducing to an identity still do after substitution, and those reducing to `a` fail at `a := K`. In general the tests differ. For example, raw `[ ] x` reads `x` from `K x`, while none of its closed instances can return that variable. The tree “Runs to I” note and its `noteTree` likewise describe direct recognition of an open subject reaching a particular closed shape. `Tree.exists_eq` is an equality algorithm on closed strict values and does not establish a closed-instance reading rule for the live figure.
- **Severity** — block
- **Suggested fix** — Define the blue predicate for general inputs by requiring the reading for every closed instance, and explain why the pictured shading agrees, or label the shading explicitly as a direct fixed-variable calculation and restrict the probe interpretation to closed inputs. Make the same distinction for the tree “Runs to I” example and both script notes. Cite only the direct claims as direct results, and give a separate invariance argument for the lifted predicate if using it.

### 5. The net panel still labels a depth-limited run as endless

- **Location** — Fibre figure, `setLevel` at line 4329, “never ends”; net counter note at line 860, “Nor is anything discarded, since the eraser of K a (ω ω) waits on its argument instead of throwing it away.”
- **Problem** — The shared level-2 annotation is rendered in net mode alongside the correctly bounded line about the last layer drawn. The five-layer graph and the 1,000-interaction trace cannot establish endlessness or permanent failure to discard. The 400-interaction trace supports the eraser remaining pending within that run. The lazy-table results cover a different, closed compilation.
- **Severity** — block
- **Suggested fix** — In net mode render “still active at the last layer shown” and qualify pending erasure by the observed prefix of the applicable run. Keep “never ends” for an explicitly cyclic strategy.

### 6. Some cycle captions still claim more than their supporting traces

- **Location** — Script lines 2506 and 2508, “over a hollow point marked no value”; line 3190, “It returns to the term it started from, so it never ends and the term has no value”; line 846, “A loop with no exit”.
- **Problem** — The SKI chosen cycle demonstrates an infinite run, and the separate leftmost-outermost argument supplies the no-normal-form conclusion. The live sentence instead infers it from the cycle. For trees, `Tree.omega_cycle` supplies a positive-length path back to the source, with no assertion about all reductions. The tree hollow point is still labelled “no value” in the fibre, running and counter views, including accessible text, although the qualified tree readout only says none is reached in the displayed graph. Both displayed cycles have steps leaving the chosen cycle.
- **Severity** — block
- **Suggested fix** — In the SKI readout separate the repeated path from the no-normal-form result and refer to the argument in the body. Use “no value reached in this drawing” throughout tree mode unless an independent tree nonnormalization argument is included and recorded. Name the loop heading by the absence of an exit to a value in the view.

### 7. The SKI fibre animation states an unconditional hole

- **Location** — Fibre figure script, line 4229, “On the right nothing fills the loop. A round trip there cannot be shrunk, and that is a hole.”
- **Problem** — This overstates the revised body and “Open” list. The figure displays an unfilled cycle. `SKI.not_absorbed'` excludes absorbing a lap by a forward continuation in the run quotient. It does not exclude a contraction using backwards steps through terms with K. The hand argument for the full fibre is conditional. The visible “hole” marker and the accessible description should have the same scope.
- **Severity** — block
- **Suggested fix** — Limit the animation, readout and accessibility text to the graph drawn or an explicitly K-free fibre. State the condition beside any depiction claimed to represent the whole SKI fibre.

### 8. The stored Lean pin differs from the requested mirror pin

- **Location** — Mechanized, line 878, “link to the statements in Lean at commit 9b151e6.”
- **Problem** — The requested command checks `refs/mirror/main` at `e945f34c0161` and fails as quoted above. The 146 essay href differences are the 144 declaration anchors and the repository and audit links. The companion’s zero-href result is a separate text-only difference in its displayed pin. This is a pin mismatch, with the declarations present at their stored lines.
- **Severity** — block
- **Suggested fix** — Have the author update both files to the intended published pin and rerun the exact requested check after the mirror ref is settled.

### 9. The new closed-instance marks outrun the linked audit

- **Location** — Mechanized, line 878, “as listed for each statement in AXIOMS.md.”
- **Problem** — The audit at the essay’s stored pin lacks per-declaration lines for `SKI.probeEqCl_of_conv`, `SKI.probeEqCl_iff_of_closed` and `SKI.probeEqCl_subst`. The summary for CI job 3172 indicates that no entry depends on `sorryAx`. That is distinct from listing the dependencies of each linked statement.
- **Severity** — should
- **Suggested fix** — Include the three audit lines from a full CI log or specify that the present file gives a CI summary for the omitted entries.

### 10. The event-permutation theorem concerns canonical labels

- **Location** — Fibre note, line 833, “fire the same interactions, possibly in a different order”; repeated in the tree-semantics status list.
- **Problem** — `Ix.Event.Run.perm` assumes `WellFormed T`, `Deterministic T` and `WF N`, and two labelled runs from the same `N` to normal endpoints. Its conclusion is `es.Perm fs` for the lists of canonical agent-pair labels. It does not equate the intermediate nets or the stateful rewrite instances in two orders. The revised body and list correctly supply the starting net and endpoints.
- **Severity** — should
- **Suggested fix** — Say “have the same canonical interaction labels, possibly in a different order” in both locations.

### 11. The snapshot test comment omits the last six intentional changes

- **Location** — `post/lab/essay-test.js`, line 9, “Review R1 changed 14 snapshots on purpose in pass G and 2 in pass D; the fixture's "source" field lists them.”
- **Problem** — The statement covers the earlier edits but omits the closed-instance update of six hashes, which overlaps the two earlier paint readout changes. The fixture’s provenance correctly states all three stages.
- **Severity** — could
- **Suggested fix** — Mention the six latest changes or refer to the fixture's source history without enumerating part of it.

### 12. Agda's default record η has an exception

- **Location** — Three equalities, line 579, “Agda gives record types η by default”.
- **Problem** — Agda’s cited documentation excludes coinductive records from that default. The normalization claim about strong sums is now scoped appropriately. [Agda record types](https://agda.readthedocs.io/en/latest/language/record-types.html)
- **Severity** — could
- **Suggested fix** — Refer to inductive record types or explicitly give the exception.

## Source checks

- The tree specification gives the five rules, credits the revised rules, and expressly uses the variable-free grammar. The classification of closed values follows in that grammar. `Tree.calculus_confluent` covers the open Lean calculus as well. `Tree.probes_read_code` proves the two identities agree in conversion after any application, are not convertible before application and are separated by a probe. `Tree.sk_unsound` gives the three pairwise separations and a counterexample when an equality includes the added rule. The tree-semantics anchors agree with the fifteen-entry eager table, closed strict evaluation soundness, the disjoint firing and normal-run results, and the closed lazy example (including the universal 27-interaction bound and the absence of infinite runs). [Tree specification](https://treecalcul.us/specification/) · [Lafont, Proposition 1 and consequence](https://core.ac.uk/download/pdf/81113716.pdf)
- The revised soundness direction agrees with the syntactic soundness proof and the semantic results. The open logical-relations statement requires a substitution satisfying Γ. The historical citations support the small-step and big-step examples without the priority language. MIT’s December 1968 report and 1969 thesis records support the distinction in the Morris note and its use of contexts. [Wright–Felleisen](https://web.eecs.umich.edu/~weimerw/2014-6610/reading/wright92syntactic.pdf) · [Milner](https://www.sciencedirect.com/science/article/pii/0022000078900144) · [RustBelt](https://pure.tudelft.nl/ws/files/40911277/popl18_p202.pdf) · [Plotkin's logical-relations report](https://homepages.inf.ed.ac.uk/gdp/publications/logical_relations_1973.pdf) · [Kahn](https://www.cs.tufts.edu/~nr/cs257/archive/gilles-kahn/natural-semantics.pdf) · [MIT report](https://dspace.mit.edu/entities/publication/0556b242-90aa-475c-b261-296f299c1ef4) · [MIT thesis](https://dspace.mit.edu/entities/publication/5fd0e97e-1b87-4fdb-9c35-8f17a42426f1)
- Huet–Lévy’s normal derivation theorem and the SKI leftmost-outermost strategy justify the separate normalization argument, and their result on orthogonal systems does not identify the repository’s run quotient with Lévy’s. The counter references prove, respectively, the count invariant on K-free terms, non-absorption in the forward quotient, and absorption for the lap under K. Girard’s Chapter 14 supports the candidate conditions. The revised polynomial cost sentence includes the input size, run length and shared normal form required by Accattoli–Dal Lago. The Lean reference supports the role of reduction, η and proof irrelevance, and Altenkirch et al. give the specific strong-sums normalization result. [Huet–Lévy, Theorem 3.26](https://www.cs.tufts.edu/comp/150FP/archive/gerard-huet/orthogonal-rewriting.pdf) · [Proofs and Types, Ch. 14](https://people.mpi-sws.org/~dreyer/tor/papers/girard.pdf) · [Accattoli–Dal Lago](https://arxiv.org/abs/1601.01233) · [Lean type system](https://lean-lang.org/doc/reference/latest/The-Type-System/) · [Altenkirch et al.](https://people.cs.nott.ac.uk/psztxa/publ/lics01.pdf)
- Turing’s §9 argument and the comparison in his JSL paper support the historical distinction between the thesis and formal model equivalence. The simulation claim in the revised essay follows directly by implementing the stated effective convention. For the PCF comparison the numerical lower bound comes from recursion and numeral operations in PCF, and the upper bound from effective evaluation, including the parallel extension. Plotkin’s examples of the added parallel operation give the higher-type separation. Jay–Vergara discuss numerical versus symbolic encodings. Fiore–Saville’s Theorem 1.1 supports the stated example about structural 2-cells. For bibliographic entries whose DOI landing page or full text was unavailable in this session I used the C-pass metadata inventory alongside the available primary copies or publisher records. [Turing, computable numbers](https://www.abelard.org/turpap2/tp2-ie.asp) · [Turing, λ-definability](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/computability-and-definability/FE8B4FC84276D7BACB8433BD578C6BFD) · [Plotkin, LCF](https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf) · [Jay–Vergara](https://arxiv.org/abs/1410.7103) · [Fiore–Saville](https://api.repository.cam.ac.uk/server/api/core/bitstreams/096d2a34-0051-4986-b7a4-474d2bf6727f/content)
