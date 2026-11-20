The frozen essay matches the working-tree file. All 89 in-repository declaration anchors match `d58539e` locally, and all eight tree-semantics anchors match `5147cfa`.
The main gaps are the scope of the probe model, open-net examples cited to closed-tree theorems, and conclusions that need hypotheses absent from the prose.
The required checker stopped at its fetch. A read-only rerun using cached mirror refs returned `140 declaration links at 33d21d5daa05; 0 problems`; that count does not check the URLs already in the files.
Of 44 distinct formal-computation declarations linked, 42 appear in AXIOMS.md with only standard axioms. The two omissions and the limits of the separate tree-semantics audit are recorded below.

## Introduction and calculus switch

- **Location** — Atoms and Probes, calculus switch, “A leaf, a stem △ u and a fork △ u v are values.”
  **Problem** — `Tree.calculus_confluent` proves joinability, while the mark follows a statement about value shapes. In the open, context-closed calculus of the figures a stem or fork can contain a redex, and a variable-headed term may be normal.
  **Severity** — block.
  **Suggested fix** — Describe the three constructor shapes and say that a value has no redex anywhere. Add “Tree reduction is confluent” immediately before the mark.

- **Location** — Atoms and Probes, calculus switch, “which has fifteen rules.”
  **Problem** — `Ix.TC.eager_sound` assumes `Tree.Eval f x v` for closed trees and proves existence of a finishing compilation with readback `v`. It gives neither the rule count nor the compiler’s treatment of open variables and free wires.
  **Severity** — block.
  **Suggested fix** — Cite `Ix.TC.eagerTable` for the rule list. Attach `eager_sound` to a separate sentence about terminating applications of closed trees, and label free-wire readback as a convention of the browser model.

## Atoms and probes

- **Location** — Atoms and probes, “the probe’s own variables.”
  **Problem** — The marked SKI results use `Reads t r := Reds t r ∧ InVars r`. `InVars` accepts every variable, regardless of whether the context supplied it. In Lean the empty probe reads an open variable already in the subject. The tree model has the same convention. Both `Probe` types also admit any number of holes. The six subjects are closed, which avoids the variable-origin discrepancy in that bench.
  **Severity** — block.
  **Suggested fix** — Define the formal observer as reading any variable-only normal form, and say that the closed bench subjects ensure those variables came from the probe. State that contexts can use the tested term more than once. If the origin restriction is essential, mark it as unformalized for open terms.

- **Location** — Atoms and probes, tree bench, “which no probe of combinatory logic can do” and “no two of the six terms are the same under probes.”
  **Problem** — `Tree.tree_six_terms` is the 24-cell tree table, not an SKI result. `Tree.tree_six_distinct` states seven separating pairs rather than all fifteen. The others follow from the shared first-three-column readings in `tree_six_terms` and uniqueness of readings.
  **Severity** — block.
  **Suggested fix** — Put the table mark on the tree readings and cite `SKI.six_terms` on the comparison with SKI. Say that the `[ ] x y` column separates the three groups, triage separates the identities within their group, and triage after `[ ] x` separates the two constant functions. Link both tree results there.

- **Location** — Atoms and probes, net bench, “the readings are those of tree calculus” and “any two runs between the same nets have the same length.”
  **Problem** — The readback comparison for open free-wire inputs is a browser check. `Diamond.equal_lengths` requires a one-step diamond and two runs from one source ending at normal forms. `Ix.Steps.equal_lengths` also requires normal endpoints, a well-formed source, and a well-formed deterministic rule table. Neither statement identifies compiled open bench cells with Lean nets.
  **Severity** — block.
  **Suggested fix** — Say that the browser computes the readings and counts for these cells. State the general theorem separately for finishing runs from the same well-formed net under a well-formed deterministic table. Record the open readback comparison and numerical counts as checks of the browser model.

## Running a term

- **Location** — Running a term, “a property called confluence.”
  **Problem** — The prose gives the literature citation, while the Mechanized table also lists `SKI.confluent`. The corresponding prose claim has no Lean mark.
  **Severity** — should.
  **Suggested fix** — Add the `SKI.confluent` mark to the confluence sentence and retain the literature note.

- **Location** — Running a term, net note, “Two interactions that can both fire can be fired in either order” and “Whichever order is chosen, the run has the same length.”
  **Problem** — `Ix.strong_confluence` gives equal successors or a common one-step successor under well-formedness and determinism. The same two disjoint firings in reverse order are the more specific `Ix.fire_commute` result. The two length marks require finishing runs. Neither proves the reachable net graph is a lattice.
  **Severity** — block.
  **Suggested fix** — Cite `Ix.fire_commute` on the commuting squares and state that all runs to a normal net have the same length under the indicated hypotheses. Describe the picture as a reachable-state graph.

## Three equalities

- **Location** — Three equalities, tree/net note, “it puts the points where sameness after running does.”
  **Problem** — `Tree.sk_unsound` separates three identities and gives a counterexample for any relation containing the added rule. It establishes neither that the two partitions coincide across the plotted bundle nor that net probes induce that partition.
  **Severity** — block.
  **Suggested fix** — State that triage keeps these three identities apart and that adding the rule joins `S K K` to `I`, which the probe distinguishes. Describe any agreement across the plotted points as an example-specific claim and give its verification status.

- **Location** — Three equalities, “since S K y x runs to x whatever y is.”
  **Problem** — The adjacent `SKI.probeEq_SK` proves contextual equivalence of the unapplied terms. The explicit reduction in the sentence is `SKI.skRun`. The reduction alone would need a contextual-equivalence argument to justify the rule.
  **Severity** — block.
  **Suggested fix** — Put the existing mark after “For every `y`, `S K y` and `I` agree under every probe.” Give `SKI.skRun` separately for the two-step application example.

## Types

- **Location** — Types, “the smallest type that contains it” and “‘Runs to I’ is a type.”
  **Problem** — `SKI.close_le` proves only the minimality inequality. The type and containment claims use `isType_close` and `le_close`. Likewise, `runsToI_not_probe` rules out a single context/reading pair and does not prove that the predicate is a type. The separate theorem is `isType_runsToI`. The same composite claims appear in the Mechanized table.
  **Severity** — block.
  **Suggested fix** — Link the three closure lemmas on the closure claim, and place separate `isType_runsToI` and `runsToI_not_probe` marks on the two parts of the second claim. Add the newly linked declarations to the audit.

- **Location** — Types, tree/net note, “‘Runs to I’ is now defined by a probe as well.”
  **Problem** — `Tree.exists_eq` produces curried structural equality for closed constructor trees under `Tree.Eval`. It supplies neither a context in this repo’s open small-step calculus that reads a variable exactly on the `I` fibre, nor a bridge for terms with no value or open normal forms.
  **Severity** — block.
  **Suggested fix** — Attribute only the closed-tree comparator to the mark. Put the probe for the full open-calculus predicate in “Not mechanized” unless a context and an iff proof are supplied.

- **Location** — Types, “S x y respects types in the same way when x and y do.”
  **Problem** — `Tree.fundamental_S` assumes specific arrow predicates for `x` and `y` and step-invariance of the result predicate `C`. The following triage mark likewise assumes branch membership at three different types and applies to constructor inputs with the required component memberships.
  **Severity** — block.
  **Suggested fix** — State the arrow hypotheses for S and the three branch obligations for triage. Give the tree `K`, `S` and triage results their own table row.

- **Location** — Types, net note, “after three interactions, and an eraser is left facing the free wire of v.”
  **Problem** — `Ix.TC.eager_sound` concerns closed trees with a strict evaluation and an existential finishing length. It neither gives three interactions nor describes an eraser stuck on an open free wire.
  **Severity** — block.
  **Suggested fix** — Attribute this to the displayed open example, with `u` and `v` explicitly free variables. List the three-interaction readback as a browser-model check.

## The definition

- **Location** — The definition, note 14, “The steps generate an orthogonal factorization system on the category of families.”
  **Problem** — The linked `beh_iff_map_bijective_co` treats step maps of a functor to sets. The unique-lifting characterization has its own result, `Presentation.beh_iff_M`. The existence of the generated factorization system is cited and is absent from the Mechanized/Not mechanized inventory.
  **Severity** — should.
  **Suggested fix** — Add the unique-lifting mark in the note with its representable-map formulation. Put the existence of the generated factorization system, under the smallness hypotheses of the citation, in “Not mechanized.”

## What a type cannot see

- **Location** — What a type cannot see, net note, “the run never ends, in any order” and “finishes in 27 interactions.”
  **Problem** — `Ix.Lazy.discarded_divergence` proves a 27-step lazy run returning a **leaf** for a specific closed suspension of self-application. The same theorem rules out a strict `EvalTm` value for that closed expression. It does not address the open eager figure’s free `a`, its three-interaction readback, persistence of readback, or every eager schedule.
  **Severity** — block.
  **Suggested fix** — Identify the open-net trace as a demonstration and report its observed prefix. In a separate sentence, state the closed lazy result with leaf output and attach the mark there. Use `discarded_every_run` if claiming schedule independence for the lazy example.

- **Location** — What a type cannot see, “Mac Lane’s pentagon axiom is the requirement that they be so counted for associativity.”
  **Problem** — `Pentagon.exists_beh_top_ne_bot` exhibits a behaviour on the opposite of the free four-letter pentagon category whose two maps differ. It does not formalize Mac Lane’s axiom or the effect of imposing it.
  **Severity** — block.
  **Suggested fix** — Attach the mark to a sentence about the separating behaviour on the free pentagon. Leave the Mac Lane claim attached to note 16.

## When probes can read atoms

- **Location** — When probes can read atoms, “a probe can take a term’s code apart” and “For terms with a value, probes that read code give sameness after running.”
  **Problem** — `Tree.probes_read_code` treats two specific identity terms. `Calculus.codeEq_iff_conv` is about `CodeEq`, which can observe any normal form directly. The tree instance’s actual `ProbeEq` observes only variable-only outputs. Separating two or three examples by triage does not prove that tree probes recover conversion for every open normalizing term. The note also appears in net mode.
  **Severity** — block.
  **Suggested fix** — Mark the two specific tree terms with `Tree.probes_read_code` and the three tree identities with `Tree.sk_unsound`. State the generic result for the explicit normal-form-reading observation. List the general tree/net triage characterization as unformalized if retained.

- **Location** — When probes can read atoms, “None of the results in this section depends on combinatory logic” and “a step is invisible to a probe however much the probe can read.”
  **Problem** — The generic results require compositional contexts, lifted reductions, confluence for conversion invariance, and normal readable outcomes. Their code-reading converse requires a normal form. They do not generalize the calculus-specific separators or `S K y` law. `SKI.codeEq_Ia_a` proves one pair, and the invariant observation reads completed normal forms rather than intermediate steps.
  **Severity** — block.
  **Suggested fix** — Name the general results individually and give their observation and hypotheses. Put `SKI.codeEq_Ia_a` immediately after the example, and use `SKI.codeEq_of_conv` if retaining the general SKI claim about normal-form readers. Scope “Any change to the text of a function” to different normal forms.

## Changing the ingredients

- **Location** — Steps are allowed in both directions, “the cost of a run is an area.”
  **Problem** — `Dehn.cost_eq_area` equates infima for deleting relators or their inverses in a free group and for products of conjugates. Free reduction is free in that model. It concerns minimal cost for words representing the identity, alongside an unqualified infimum equality in Lean. It is not an equality for each individual run or for the browser grid’s adjacent swaps.
  **Severity** — block.
  **Suggested fix** — Say “For a word representing the identity, the least number of relator deletions, with free reduction free, is its area in the presentation.” Use that scope in both prose occurrences and the table. List the grid area calculation separately as an elementary unformalized example.

- **Location** — Changing the ingredients, “stay apart and can return evidence changed” and “The third is the whole gap between probes and running.”
  **Problem** — `Pentagon.top_ne_bot_localized` distinguishes localized maps but does not supply the behaviour asserted in the same sentence. `Calculus.codeEq_iff_conv` only closes the gap for the explicit full-normal-form observer when one input reaches a normal form. Also, `Calculus.probes_invariant` establishes invariance from confluence and stable outcomes. The implication in the following sentence uses `Calculus.probeEq_of_conv`.
  **Severity** — block.
  **Suggested fix** — Add `Pentagon.exists_beh_top_ne_bot` to the evidence clause. Mark each probes claim with its matching statement and replace “the whole gap” with the qualified normal-form-reading result.

- **Location** — A fibre over a value, tree/net notes, “they all count as one,” “any two of them differ by squares,” and “ten interactions.”
  **Problem** — The tree claim is unmarked, and the linked `Tree.omega_cycle` concerns a different example. `Ix.fire_commute` proves a local square for two disjoint enabled firings, not a result about all routes. `Diamond.equal_lengths` supplies no concrete length. `Ix.Event.Run.perm` states permutation of event lists for complete runs from the same well-formed source under a well-formed deterministic table, without verifying the open browser example.
  **Severity** — block.
  **Suggested fix** — Label the three tree routes and their proposed identification as an unformalized example. Give the net claim for finishing runs with the appropriate theorem and report ten as a browser-computed count. Use `fire_commute` only for the individual squares.

- **Location** — A fibre with no value, net notes, “it does not loop but grows” and “the net of ω ω has no loop to go round.”
  **Problem** — The lab notes record a finite check of one outermost schedule. The cited net theorems do not rule out repetition at every depth or under all schedules. Even absence of directed cycles would leave open holes involving backward steps.
  **Severity** — should.
  **Suggested fix** — Report that no repeat appeared in the first thousand interactions of the outermost run. Remove the conclusion about holes or state it as an open question. Apply the same scope to “its net never stops growing” in the earlier note.

- **Location** — Changing the ingredients, after the two fibres, “a fibre in which every term has a single run to one term, so counted, has no holes, and a behaviour over it amounts to evidence about that term.”
  **Problem** — The inline mark points only to the behaviour equivalence. `beh_equiv_type_of_terminal_co` assumes a terminal object and `𝒜.steps = ⊤`. The localization result is separate. The conclusion about bare evidence does not follow merely from being hole-free if the chosen steps do not generate the runs.
  **Severity** — block.
  **Suggested fix** — Specify the category of counted runs with all its arrows inverted. Link `localization_trivial_of_terminal` on absence of holes and `beh_equiv_type_of_terminal_co` on the equivalence with sets when all arrows are inverted. Retain the qualification about the unformalized Lévy bridge.

- **Location** — Changing the ingredients, counter notes and explanation, “every run between two nets has the same length,” “The number of interactions is a behaviour,” and “a lap there has to count for nothing.”
  **Problem** — Equal lengths of finishing runs do not prove a global net counter behaviour or the assertion that there is no second route. A bijective counter increment needs evidence such as integers. The tree absorption claim is also unmarked and unformalized here. In SKI, `absorbed` proves equality for the other order of the I-steps, and `omegaLoop_permEq` is needed for the lap drawn.
  **Severity** — block.
  **Suggested fix** — Restrict the net statement to finishing lengths, or supply a separately stated integer-translation behaviour proof for a precisely specified category. Record tree absorption as unformalized. Link `omegaLoop_permEq` alongside `absorbed` for the drawn SKI lap.

- **Location** — Changing the ingredients, counter explanation, “On the three terms of the left-hand panel the counter is a behaviour” and “so that no run out of ω ω undoes a lap.”
  **Problem** — `SKI.omegaLoop'_wt` proves only that the chosen lap has weight one. The result that weight respects `PermEq` requires a K-free source, and `not_absorbed'` specifically forbids equality after a common forward continuation. Neither alone states that the loop survives inversion. The unqualified later “is not filled and has no exit” also conflicts with earlier acknowledgement of steps outside the drawing.
  **Severity** — block.
  **Suggested fix** — Put the weight mark on the lap increment, the invariance mark on the K-free statement, and `not_absorbed'` on non-absorption after a forward continuation. State the localized-hole question as open, as the status list already does, and distinguish steps out of the pictured cycle from reaching a value.

## Mechanized

- **Location** — Mechanized, “The results on probes hold in any confluent calculus whose steps can be taken inside a probe.”
  **Problem** — The row bundles different hypotheses and conclusions. It can also be read as generalizing the bench, nondefinability example and tree triage results. `Calculus.probeEq_plug` follows from compositional plugging even without confluence. `Calculus.codeEq_iff_conv` compares `CodeEq` with conversion and assumes a normalizing input.
  **Severity** — block.
  **Suggested fix** — Name the three specific results in the row and give the hypotheses for each. Include the invariant pairing separately if the four-properties discussion keeps its mark.

- **Location** — Mechanized, “Claim in the essay” and “Not mechanized.”
  **Problem** — The status inventory omits most switch results and blurs the numerical net examples, verified general theorems and open claims. It also omits the definition of observation as a pairing and the distinction between its standalone Lean model and the presentation structure.
  **Severity** — should.
  **Suggested fix** — Add rows for the tree bench and pair separation, the unsound tree rule, tree K/S/triage, the witnessed five-step cycle, and the applicable net normal-run and commutation theorems. List the closed comparator, compiler soundness and closed lazy example under tree-semantics. Add the browser-only open-net readbacks and counts, tree route and lap identifications, global net repetition/hole and counter claims, and the full tree/net code-reading and runs-to-I characterizations to the status list. Link `Obs.Pairing` on the abstract observation definition and identify the three-ingredient presentation as the essay’s formulation. Give the cited formal examples on the cards, including the grid and trace-versus-bisimulation, an explicit status.

- **Location** — Mechanized, “the list for each statement is in AXIOMS.md.”
  **Problem** — Two linked declarations are missing from the pinned formal-computation audit, `SKI.probePred_respects` and `SKI.omegaLoop'_wt`. The entry `SKI.omegaLoop_wt` is for the other lap order. All other 42 linked declarations in this repo are listed and use only a subset of `propext`, `Classical.choice` and `Quot.sound`. The six external declarations are outside that audit. The tree-semantics clone has an audit driver with entries for `Ix.fire_commute`, `Ix.strong_confluence`, `Ix.TC.eager_sound` and `Ix.Lazy.discarded_divergence`; it does not list `Ix.Steps.equal_lengths` or `Tree.exists_eq` by name. The driver is not emitted axiom output.
  **Severity** — should.
  **Suggested fix** — Audit the two missing local declarations in CI and update the pinned audit. Limit the published guarantee to results with audit output and cite exact external audit results if claiming the guarantee for tree-semantics.

- **Location** — Mechanized, “at commit d58539e.”
  **Problem** — The requested checker target was `33d21d5`, but the frozen essay and companion actually use `d58539e`. The exact command `python3 -I scripts/lean-links.py 33d21d5 --check` exited 1 with `subprocess.CalledProcessError: Command '['git', 'fetch', '-q', 'github']' returned non-zero exit status 255.` With the fetch bypassed in memory and the cached ref used, it printed `140 declaration links at 33d21d5daa05; 0 problems`. At the actual pin it printed `140 declaration links at d58539e1b007; 0 problems`. The checker computes but never compares replacement text in check mode, so zero problems at `33d21d5` does not validate the stored pin. A direct anchor comparison verified all 89 essay declaration URLs at `d58539e`. The Lean source and audit bytes match across both local pins.
  **Severity** — should.
  **Suggested fix** — Use the actual publication pin for the stated check, or explicitly repin the files if `33d21d5` is intended. Make check mode report stored URL, pin, and line differences from the computed replacements. Check the external anchors separately as in this pass.

## Footer

- **Location** — Footer, “the table of six terms and the claims about probes, including probes that read code, for combinatory logic, for tree calculus and for any confluent calculus with probes.”
  **Problem** — The mechanization claims in the footer have no direct marks. The blanket wording extends the generic theorems to calculus-specific results, and “The cards on cost, higher types, processes and proofs have not been mechanized” sweeps in the cited finishing-length theorem on the cost card.
  **Severity** — should.
  **Suggested fix** — Link the specific footer claims and qualify the general code-reading theorem by reachability of a normal form. Name finishing interaction counts as a mechanized result under the table and source hypotheses, and distinguish it from the broader cost-card argument.
