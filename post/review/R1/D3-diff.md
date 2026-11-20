# R1 D3 · Diff check

Reviewed `b553b19..d9281a6` for the essay and SKI snapshot fixture. **3 block, 2 should, 0 could.** The required link check still fails. The hand-argued status list overstates the closed-instance predicate, and two tree views still present the absence of a normal form as established by the figure. The snapshot delta matches its provenance exactly.

## D2 findings

| D2 finding | Status | Evidence at D3 |
|---|---|---|
| 1. Introductory reading rule | Resolved | “A probe is run only on a term without variables of its own” precedes the worked example. “Made in both at once” specifies a shared closing substitution, and “It can try another context instead” gives the correct range of experiments. The direct fresh-variable rule is presented as an alternative. |
| 2. Relations and theorem marks | Partly resolved | “Through closed instances and compared directly” now links both congruence statements in the table. The main conversion sentence links `SKI.probeEqCl_of_conv`, and “so does any replacement of their variables” accounts for `probeEqCl_subst`. The generic recap spells out composition. The first generic statement still calls the bare hole “an empty context”, and the observation recap gives a direct-reading mark for the adopted rule. See finding 4. |
| 3. Tree code-reading scope | Partly resolved | “With I for a and K for b, the probe [ ] x y reads x y from one and x from the other” fixes the tree example. “The loop would agree both with I and with K” supplies the separate loop argument. The body and table distinguish direct SKI code readback, but the live readout still says “Sameness under probes now agrees with sameness after running.” See finding 5. |
| 4. Predicates on open subjects | Partly resolved | “The figure, computed in the browser, applies the probe directly to each term, those with variables included” distinguishes the calculation from the open-input definition, and the direct Lean marks are qualified. The status list says “gives the verdict of every closed instance”, and the tree note says “every closed instance runs to I exactly when the term does”. See findings 2 and 3. |
| 5. Bounded net run | Resolved | “Still active at the last layer shown” replaces “never ends” in net mode, and “up to its cap of 400 interactions” bounds the eraser claim. The replay fired no erase rule in that prefix. |
| 6. Cycle captions | Partly resolved | The SKI readout now says “That the term has no value is argued in the text”, and the tree caption says “no value reached in the terms drawn”. “Only the values are left” still says of the hollow point that it stands for “the terms that have none”. See finding 3. |
| 7. SKI fibre animation | Resolved | “On the right nothing fills the cycle drawn” sets the scope of the visible hole marker. The readout calls the full-fibre claim an argument “only under an assumption, which is open”. The SVG description likewise says “nothing fills in the graph drawn”. |
| 8. Lean pin | Unresolved | “Link to the statements in Lean at commit bd254f3.” The requested check against `7cccf0f` exits 1. See finding 1. |
| 9. Axiom audit | Resolved | “As listed for each statement in AXIOMS.md” is now backed at the stored pin by the entries for `SKI.probeEqCl_of_conv`, `SKI.probeEqCl_iff_of_closed` and `SKI.probeEqCl_subst`. |
| 10. Event labels | Resolved | Both locations say “carry the same interaction labels, possibly in a different order, where a label names the two interacting agents by canonical names”. |
| 11. Snapshot test comment | Resolved | “Review R1 and its follow-ups changed some snapshots on purpose; the fixture's "source" field lists each change.” |
| 12. Agda default η | Resolved | “Agda gives record types η by default, except coinductive records.” [Agda record types](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion) |

## Items marked partly resolved in D2’s earlier-findings table

| Original finding | Status | Evidence at D3 |
|---|---|---|
| D1. Tree triage and open normal forms | Resolved | “On closed terms, one of which has a value” scopes the intrinsic characterization. “One replacement already separates a from b” supplies the witness under the adopted comparison. |
| D2. Fixed-variable type test | Partly resolved | “A term with variables when the probe reads x from every closed instance” gives the intended quantifier. The status list says “gives the verdict of every closed instance”. See finding 2. |
| D3. Generic probe theorems | Partly resolved | “Both results compare terms directly, without closed instances” and “putting a term in it is putting the term in the inner context and the result in the outer one” distinguish the relations and give the composition law. “It has an empty context” and the direct invariant mark could still be made precise. See finding 4. |
| D5. Normal net runs and event permutations | Resolved | “Runs from one net that finish in an irreducible net” supplies the common source and endpoints. “A label names the two interacting agents by canonical names” fixes the event claim. |
| D7. Bounded net observations | Resolved | “Still active at the last layer shown” and “up to its cap of 400 interactions” bound both remaining statements. |
| D8. Cycle and no-value claims | Partly resolved | “A hollow point marks the fibre with no value reached in the terms drawn” qualifies the tree caption. The tree “Only the values” readout still calls those “the terms that have none”. See finding 3. |
| D9. Conditional full SKI hole | Resolved | “In the graph drawn a round trip cannot be shrunk” scopes the animation, and the same note makes the whole-fibre claim conditional. |

## Remaining findings

### 1. The required pin check fails

- **Location** — Mechanized, line 878, “link to the statements in Lean at commit bd254f3.”
- **Problem** — The requested mirror pin is `7cccf0f89a31`. The essay stores 146 declaration links plus the repository and axiom-audit links at `bd254f3`. The companion’s “0 stored link(s)” diagnostic counts HTML hrefs, so it does not count the companion’s Markdown link changes or its displayed commit.
- **Severity** — block
- **Suggested fix** — Update both files to the requested published pin and rerun the exact command below.

### 2. The two predicate claims need the universal test scoped explicitly

- **Location** — Mechanized, line 930, “applying the probe of ‘returns its argument’ directly gives the verdict of every closed instance”. Types, line 598, “on the terms of the figure every closed instance runs to I exactly when the term does”.
- **Problem** — The direct verdict on the displayed term `a` is negative for both predicates. With `a := I`, that instance runs to `I` and `[ ] x` reads `x`. With `a := K`, the instance fails both tests. Thus the direct verdict agrees with the universal test in this example, while instances can individually disagree with the direct verdict. Line 601 gives the right universal definition, but the SKI live note at line 3554 stops at “This predicate is defined by the probe [ ] x with the reading x.”
- **Severity** — block
- **Suggested fix** — Say that the direct test passes on a displayed term exactly when **all** its closed instances pass. In the SKI live note, identify the calculation as direct and scope agreement to the terms drawn, as the tree note already does. For tree ‘Runs to I’, steps to `I` survive substitution, and each pictured open term that runs to `a` has the failing instance `a := K`. The closed terms are unchanged by substitution.

### 3. The tree figure still asserts global lack of a normal form

- **Location** — Running, line 3201, “Only the values are left. The picture is now a partial function from terms to values, and the hollow point stands for the terms that have none.” Types, line 3552, “has a normal form”.
- **Problem** — The first readout also runs in tree mode. The second predicate excludes every node assigned to the hand-supplied loop group using `n.f !== 'loop'`. Neither the displayed five-step cycle nor `Tree.omega_cycle` excludes a normalizing path. The new blue-predicate note also needs a reason that the capped tree calculation's negative verdict for `(ω ω) x` is the actual probe verdict.
- **Severity** — block
- **Suggested fix** — Scope the tree readout and the predicate to normal forms reached in the drawing, or give a separate tree nonnormalization argument and cite it in both places. One possible invariant is to take the terms generated by `ω`, `I u`, and `K u (△v)` with `u,v` in that family. A step inside the family stays in it, since an identity wrapper expands to a K wrapper and the K wrapper reduces to its first argument. In a reduct of `ω ω` the two factors stay in that family. Application of a left factor `ω` makes two identity wrappers, and a left factor with either wrapper has a redex in the wrapper. This also leaves a redex in every reduct of `(ω ω) x` and gives the needed negative verdict without a depth bound.

### 4. State the bare-hole law and carry the closed-instance argument into the recap

- **Location** — When probes can read atoms, line 693, “it has an empty context, a context can be put inside another, its steps can be taken inside a context, and its readable outcomes take no step.” Observation recap, line 775, “A step in the term under test never changes a probe’s reading.”
- **Problem** — The generic result is correctly limited to `Calculus`, but “empty context” could be read as having no holes. `Calculus.codeEq_iff_conv` uses the context consisting of one bare hole and the law `plug hole t = t` to recover conversion from a reading. The recap’s `SKI.probes_invariant` mark uses direct `Reads`. Its application to the adopted rule follows by the closing-substitution argument at line 575.
- **Severity** — should
- **Suggested fix** — Name the bare hole and its identity law in the first generic statement. In the recap, attach `probeEqCl_of_conv` to the SKI closed-instance claim or state that the direct invariant is applied after each common closing substitution. The quantifier definition itself can link to `SKI.ProbeEqCl` at `Closed.lean:114`.

### 5. The live SKI code readout omits the theorem’s scope

- **Location** — Code-reading figure, line 3517, “A probe that can read a normal form separates I, S K K and S K S. Sameness under probes now agrees with sameness after running.”
- **Problem** — The first sentence is supported by reading the three distinct normal forms in the bare hole. The second reads as an unrestricted theorem. `SKI.codeEq_iff_conv` requires that one term have a reachable normal form and reads open terms directly. The body at line 692 and the Mechanized table now give those qualifications.
- **Severity** — should
- **Suggested fix** — Bring the same qualifications into the live readout. Say that the checkbox reads normal forms directly, variables included, and that its readings determine conversion when one term has a value.

## Changed-claim checks

- **Reading and equivalence, lines 477–478, 572, 575 and 578.** The common-substitution wording matches `SKI.ProbeEqCl`, and the two closed Lean relations coincide by `Closed.lean:131`. The strict alternative agrees on closed inputs because the subject contributes no variables. Direct calculation gives `I x → x`, `K I x → I` and `K I x y → I y → y`. `Closed.lean:388` supports the permissive `a I` and `a K` example, while `Probes.lean:349` covers the six terms. In trees, if the closed loop agreed with both instances of `a`, transitivity would equate `I` and `K`. Their two readings, `x y` and `x`, refute this. `Tree/Essay.lean:182` establishes unsoundness of the new rule on closed witnesses. `Closed.lean:127` handles conversion of open SKI subjects via `conv_subst`, and the generic direct proof lifts reductions into contexts and uses confluence and normality of readings. `Probes.lean:330` can be instantiated with each substituted `y`, and `Types.lean:93` gives the two-step run. The Morris reference supports the contextual method. The closed-instance restriction is identified as the essay’s variant. [MIT report record](https://dspace.mit.edu/entities/publication/0556b242-90aa-475c-b261-296f299c1ef4)
- **η, line 579.** The added coinductive exception agrees with Agda’s documentation. [Agda record types](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion)
- **Predicates, lines 598, 601, 889, 930 and 3551–3555.** At `tree-semantics` `5147cfa`, `Programs.lean:256` states a strict equality program over closed trees. The essay separately argues how to return a fresh variable on matching the entire closed shape of `I`. `SKI/Probes.lean:370,375,379,386` support the direct predicate and its invariance, the type of terms reaching `I`, and the nondefinability in SKI. The last also follows in the closed-instance observation because its two witnesses are closed. The browser uses a fixed `x`, with a 60-step cap in tree and net modes on the tree bundle. The identity cases return `x`. The open terms that reduce to `a` admit a negative witness by substituting `K`, and the tree loop needs the argument in finding 3. The quantifier defect is in finding 2.
- **Reading code and generic context laws, lines 690, 692–693, 775, 884–885, 887, 890, 896 and 903–905.** `Tree/Calculus.lean:425` gives the two identities’ argument agreement, conversion separation and probe separation. The concrete branch test distinguishes leaf from stem, and the bench confirms the three triage readings. The closed `I` and `K` readings also separate the open variables with one common substitution. Closed tree values can be matched down to all leaves, so matching a fixed value suffices when either side has that value. `SKI/Probes.lean:405,410,417,422` support full normal-form readback, with its normal-form premise for the equivalence, and the examples. `Calculus.lean:154,188,193,217` give conversion invariance, context congruence, invariant pairing and full readback. Their required laws are in the structure at line 39. `SKI/Closed.lean:127,131,142,148,239,388` distinguish conversion, agreement on closed terms, substitution stability, context stability, and the two counterexamples. `SKI/Confluence.lean:160,240` supports confluence and the three distinct conversion fibres. See findings 4 and 5 for the remaining wording.
- **Cycles, labels, net runs and event lists, lines 550, 826–827, 833, 847, 860, 922, 2506–2508, 2827–2841, 3196, 3474–3477, 4235, 4240, 4271, 4316, 4335 and 4416.** The tree labels now describe the drawing, and a strategy that repeats a chosen cycle gives an infinite run along that cycle. The SKI readout separately invokes the text’s nonnormalization argument. `SKI/Types.lean:118` excludes absorption by any forward continuation and supports the revised animation sentence at that scope. `IxCommutation.lean:96`, `IxConfluence.lean:278,308` and `IxEventPerm.lean:92` at `5147cfa` give disjoint commutation, the immediate-result or one-more-step diamond, equal lengths and permutation of canonical labels under their stated hypotheses. `Diamond.lean:90` supplies the generic equal-length result. The embedded reducer replay gave 44 reachable states with one irreducible net at depth 10 for `K a (I b)`, 1,001 distinct state keys through 1,000 outermost interactions on `ω ω`, and no erase rule through 400 interactions of the eager `K a (ω ω)` run. The stub-DOM bench independently checks all 24 displayed tree and net reading pairs. Finding 3 covers the residual global tree claim.
- **Pins and audit, line 878 and href-only edits.** I read the declaration statements at the stored href commits using the local Git objects. All 146 formal-computation declaration anchors and 23 tree-semantics anchors land on declarations, representing 60 and 9 distinct targets respectively. The axiom audit at `bd254f3` includes the closed-instance statements identified by D2. The exact pin check below is a separate failure. No Lean or Lake command was run.

## Required link check

`python3 -I scripts/lean-links.py 7cccf0f --check` exited **1**.

```text
197 declaration links at 7cccf0f89a31; 2 problems
  post/atoms-and-probes.html: 148 stored link(s) differ from the pin 7cccf0f89a31 (re-run without --check)
  post/technical-companion.md: 0 stored link(s) differ from the pin 7cccf0f89a31 (re-run without --check)
```

## Snapshot check

Compared the parsed fixture at both Git revisions. The same 1,118 keys exist at each. Exactly 14 hashes changed, seven per width. At both 1200 and 400, those keys are `fib 1 #fread` and `#fib-w` for `load`, `fib 0`, `fib 1`, `fib 2`, `fib 3` and `fib play`. They match the D2 update in the fixture’s `source` field. Comparing the two revisions’ serialized scenarios also confirmed that the twelve `#fib-w` changes are confined to `aria-label`, and the two readouts carry the revised claim about the hole. The read-only stub-DOM harness reported **256 checks passed, 0 failed**, with **1,118/1,118** snapshot matches on load and after switching back to SKI.
