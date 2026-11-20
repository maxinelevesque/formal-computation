R1 · N · Frozen essay `7626ff8`, read with the figures in Combinators, Trees and Nets.
The small combinatory examples give the essay a clear spine. The gaps are at the transitions from probe readings to type tests, from individual steps to equations between runs, and from machine states to the numerical line.
Tree notes work best when they walk through one changed example. Net notes need a local cue for which figures show nets, which show tree terms, and what counts as a reading.
The most important recaps are the literal meaning of the line, the rule for identifying runs, and the scope of the counter and cost examples.

## Opening

- **Location** · Opening, “Black is for what is kept, which is the line and its points.”
  - **Problem** · The first legend asks readers to recognize a technical object before the essay gives it a meaning. The bench then numbers points before a line is drawn.
  - **Severity** · should
  - **Suggested fix** · Add ‘Each point stands for a group of descriptions counted as equal. The line draws those groups side by side.’

## Two accounts of a typed program

- **Location** · Two accounts of a typed program, “Others can pass over it”
  - **Problem** · The skip instruction sends general readers past the introduction of `⟦A⟧`, arrow types and the fundamental lemma, all needed in Types. ‘The object that a parser returns’ also assumes programming vocabulary.
  - **Severity** · should
  - **Suggested fix** · Keep the two displayed judgments with their plain readings. Make the derivation detail optional and describe a parsed term as the tree obtained by grouping its symbols.

## Atoms and probes

- **Location** · Atoms and probes, “it may read only what it supplied”
  - **Problem** · The distinction between variables in the original term and variables introduced by the probe is essential and easy to miss. The spellings `x` and `y` also appear as placeholders in rules. An outcome with an original free variable and no constant is left unexplained.
  - **Severity** · block
  - **Suggested fix** · Say that rule letters stand for arbitrary terms and that each probe introduces fresh names. For `[ ] x`, show that a final `x` is readable and an original free `a` is unreadable, even though neither contains a constant. State how an unreadable normal form and a run with no normal form are reported.

- **Location** · Atoms and probes, “For these six the three contexts are enough”
  - **Problem** · The bench establishes three sample readings. The later converse argument needs agreement in every context, and the only general justification is the Lean marker. The reason that application agrees is also needed when the rule `S K y → I` is added.
  - **Severity** · block
  - **Suggested fix** · Give a one-paragraph explanation for the two merged groups. Show that the three identities all return their argument, that `K` applied to any of them discards one argument and leaves that identity, and explain why wrapping, copying or discarding those terms can expose no extra readable symbol under the black-box rule.

- **Location** · Atoms and probes, “Six terms under three probes”
  - **Problem** · Trees and Nets show a fourth column and five displayed points. The note eventually explains that the remaining pair is separated by an unshown probe. In Nets, that pair already has unequal visible counts, 9 and 10 under `[ ] x y`, yet shares point 4. The caption's ‘same readings in every column’ gives no way to interpret that row.
  - **Severity** · should
  - **Suggested fix** · Use ‘Four displayed probes’ in those modes and label the last column ‘Point by displayed readings’. Add ‘Small numbers give interaction counts. The points group by returned readings.’ Point forward to the cost card if the reader wants to treat the counts as answers.

- **Location** · Atoms and probes, “Its outer part asks that branch’s shape”
  - **Problem** · The tree note opens with a long compound term and assumes the reader can recover the five rules and tree abbreviations from the header, before the essay has taught the SKI ones. The net header similarly uses ‘principal ports’, ‘result port’ and ‘eager table’ without an example.
  - **Severity** · should
  - **Suggested fix** · Lead with ‘Take the right branch, then use its shape to choose x, y or z.’ Supply one worked row and move the full probe to a note. In Nets, use the selected experiment to point out the result wire and the two connectors that meet for one interaction.

- **Location** · Atoms and probes, “A positive type, such as a sum”
  - **Problem** · Polarity appears as an unexplained consequence of the atom/probe distinction. Calling elimination forms atoms that build a probe does not explain why application is both an atom and part of a probe. The paragraph is legible chiefly to type theorists.
  - **Severity** · could
  - **Suggested fix** · Keep one example: ‘A pair is built by pairing and tested by asking for either component. Applying a function is a test of what it does.’ Put the polarity classification in the sidenote.

## Running a term

- **Location** · Running a term, “The term K a (I b) has two”
  - **Problem** · A run has just been defined as any sequence of steps, so prefixes also qualify. ‘Both runs end at a. In this calculus that always happens’ initially reads as a termination claim, just before a divergent example. The imported word ‘value’ also needs to cover open normal forms such as `a`.
  - **Severity** · should
  - **Suggested fix** · Say ‘There are two runs all the way to a normal form’ and ‘Confluence means any two finite runs can be extended to meet’. Add that `a` is a normal form because variables have no rule.

- **Location** · Running a term, “The figure has five”
  - **Problem** · This counts displayed components, then calls one a fibre holding three terms, even though the note says it has further steps. The caption’s single hollow point can also suggest that all valueless terms are convertible. In Nets the figure shows one selected term, the states are nets, and the repeated ‘Only the values’ control has to distinguish a stable result from a finished run.
  - **Severity** · should
  - **Suggested fix** · Say ‘The SKI drawing shows representatives of five fibres. A hollow point marks a displayed fibre without a value.’ In Nets state before the controls that each box is a whole net and that a result at its output can precede completion. Say that the eager `ω ω` net keeps growing, using ‘loop’ for the SKI or tree term cycle.

## Three equalities

- **Location** · Three equalities, “A proof assistant decides this equality by running both sides”
  - **Problem** · The preceding section established confluence and allows terms with no value. Confluence alone gives no decision procedure by normalization there. The later addition example also uses ‘propositional’ as if it named exactly the cases normalization cannot decide.
  - **Severity** · should
  - **Suggested fix** · Scope the comparison to a checker with terminating normalization for the terms it compares. Introduce propositional equality as a statement one can prove, and use `x + 0 = x` as a case where the checker needs a proof.

- **Location** · Three equalities, “makes a function f interchangeable with the abstraction λx. f x”
  - **Problem** · The comparison assumes λ notation and free versus bound variables. The section before the intervening Running section only names `λ`, so this is both a missing introduction and an unassisted return to the function-as-use distinction for non-PL readers.
  - **Severity** · should
  - **Suggested fix** · Read the expression aloud as ‘the function that takes a fresh x and returns f applied to x’. Replace ‘where a type has such a rule among its steps’ with ‘when the calculus gives terms of that type such a rule’.

- **Location** · Three equalities, “The rule S K y → I is therefore unsound here”
  - **Problem** · The tree note and the body give opposite verdicts on the same checkbox, and Nets renders the tree-term graph. The tree note itself gives a useful recap of triage with `x`, `y`, `z`, but the imperative ‘Tick the box’ is followed by the SKI outcome unqualified.
  - **Severity** · should
  - **Suggested fix** · Begin the paragraph ‘In Combinatory logic, tick …’. Put ‘See the same rule break the tree test’ next to the Trees control. In Nets label this view as tree-term equalities seen through the compiled probes.

## Types

- **Location** · Types, “A reducibility candidate, for instance”
  - **Problem** · ‘Head expansion’, ‘neutral term’, ‘one-step reducts’ and ‘biorthogonal’ are unexplained. The example then needs a recall of `ω = S I I` and of the looping argument from Running, two sections back. Its decisive contrast, that there is both a step to `a` and a way to run forever, is left for the later figure.
  - **Severity** · should
  - **Suggested fix** · Keep the contrast in the body: ‘Some type interpretations require every run to end. K a (ω ω) can step straight to a or run its argument forever, so that condition can distinguish the two.’ Put the three specialist conditions in the sidenote.

- **Location** · Types, “the predicate defined by a probe”
  - **Problem** · `[ ] u v` now supplies arbitrary terms and asks whether the plugged term is in `⟦A⟧`, even when there is no readable result. The quantification over all admissible `u` and `v` is also more than one experiment. The earlier probe definition cannot justify the argument as stated.
  - **Severity** · block
  - **Suggested fix** · Define an application test with specified input predicates and an output membership check. Call `⟦A → B → A⟧` the predicate of passing every such test. Explain that this uses the same plugging operation as the bench with a different verdict. Apply that distinction to the figure and to ‘The definition’.

- **Location** · Types, “‘Runs to I’ is now defined by a probe as well”
  - **Problem** · The tree note relies on code-reading before its body explanation. It says the probe compares a value to `I` but leaves unstated how the comparison becomes an allowed reading. ‘Equality of code’ can also sound like comparing the input text before running.
  - **Severity** · should
  - **Suggested fix** · Give the experiment in order: run to a tree value, compare that value with `I` using shape tests, and return a fresh supplied marker on a match. No value or no match yields no marker.

- **Location** · Types, “The net of △△ u v reads u at its result port after three interactions”
  - **Problem** · The Nets lemma panel and ‘Back across the step’ still show a single tree K-step. The note gives a three-interaction result with a leftover eraser but no link between that result and the type argument.
  - **Severity** · should
  - **Suggested fix** · Label the panel ‘Tree-level type argument’ in Nets. Say that the compiled example exposes `u` at its output after three interactions and still has an erasure obligation. Reserve the backward step proof in the figure for the tree rule.

## The definition

- **Location** · The definition, “A family may attach evidence to a term”
  - **Problem** · The body defines assignment but omits the transport maps that a family has. ‘Exactly one way’ then sounds like evidence has a unique inhabitant, or that a destination can be inferred from the two sets alone. The precise meaning is available only in the category-theory note.
  - **Severity** · block
  - **Suggested fix** · Say ‘A family gives each term a set of possible evidence and each step a map carrying evidence forward. Transport along a run composes its step maps. In a behaviour each map is invertible.’ For a predicate use a singleton at a satisfying term and the empty set otherwise.

- **Location** · The definition, “Subject reduction and subject expansion”
  - **Problem** · These names enter without a plain reading, and ‘the half’ leaves it unclear which direction each names. ‘Reflector’ in the table names a construction the body never uses.
  - **Severity** · could
  - **Suggested fix** · Gloss preservation forward as reduction and preservation backward as expansion. Use ‘Closure’ in the table, with ‘reflector’ in the specialist note if needed.

## What a type cannot see

- **Location** · What a type cannot see, “It records which fibre a term is in”
  - **Problem** · A single predicate can cover several fibres, so knowing its yes/no answer cannot in general recover the term’s fibre. The earlier shading paragraph gets this distinction right. The summary repeats the stronger phrasing.
  - **Severity** · should
  - **Suggested fix** · Use ‘Membership depends only on the fibre’ here and in Summary. Retain the example of one predicate shading several identity fibres.

- **Location** · What a type cannot see, “The point shows neither the two routes nor the loop”
  - **Problem** · The Nets panel shows a stable result beside continuing work. Its common title and caption still promise a loop and the following paragraph describes an outermost exit. The net note is a good contrast when read alone, but the reader has to infer which account the caption means.
  - **Severity** · should
  - **Suggested fix** · In Nets call the right panel ‘An answer before the run ends’ and key the caption to its two displays, the result wire and the continuing interactions. Introduce the following evaluation-order paragraph as the SKI case.

- **Location** · What a type cannot see, “unless the two runs are counted as one”
  - **Problem** · The checkbox and the Mac Lane reference give opposing examples of a distinction before the essay says what it means to equate runs. A reader cannot infer from shared endpoints that transport agrees, or tell what the checkbox is assuming.
  - **Severity** · block
  - **Suggested fix** · Explain before the figure that a calculus may declare two routes interchangeable, which requires every evidence transport to respect the declaration. For the pentagon say that associativity coherence expressly makes the two routes interchangeable.

## When probes can read atoms

- **Location** · When probes can read atoms, “The checkbox marked ‘Let probes read code’, under the table”
  - **Problem** · The reference names the old control and restates the old variable restriction, but it does not disambiguate what ‘read the term itself as it stands’ meant in Atoms and probes. Reading the input tree would separate `I a` from `a` and defeat this section's key distinction. The tree note says both that the box is ticked and that no checkbox is needed.
  - **Severity** · block
  - **Suggested fix** · At the first checkbox and here, say ‘Read the whole normal form after running, including its constants.’ Use a local label ‘Tree triage already reads normal forms’ for the fixed setting and name the restricted/unrestricted contrast as a SKI experiment.

- **Location** · When probes can read atoms, “There application is the only probe”
  - **Problem** · Earlier a probe is an arbitrary permitted context with a verdict. Here ‘application’ could mean one operation for building tests or the entire class of contexts. The earlier λ and η material, more than a section back, gives no local explanation of what observations the comparison allows.
  - **Severity** · should
  - **Suggested fix** · State the particular black-box observation meant: a function is tested by applying it to arguments and observing returned results. Relate this directly to the earlier identity examples.

## Changing the ingredients

- **Location** · Changing the ingredients, “a description is a tape with a head and a state”
  - **Problem** · The next sentence about the line identifies programs with partial functions without saying how programs relate to those descriptions. A machine configuration and a machine encoding an entire function are different things. ‘Universal’ is also defined here only by reaching every partial recursive function, which does not on its own imply that all universal calculi have exactly the same points.
  - **Severity** · block
  - **Suggested fix** · Say that a machine program specifies the move rules, and that each supplied input determines a starting configuration for that program. Define the numerical line by grouping programs with the same partial input/output function. Distinguish the equivalence theorem for the named models, the thesis about effective computability, and universality within that effective setting.

- **Location** · Changing the ingredients, “No card changes the descriptions”
  - **Problem** · In an essay whose global control is advertised as changing calculus, this reads as a retreat from the demonstration. The cards themselves name words, nets, processes and proofs in place of SKI terms.
  - **Severity** · should
  - **Suggested fix** · Say ‘The cards highlight one changed choice at a time. The calculus switch also changes which objects serve as descriptions, from SKI terms to trees or nets.’

- **Location** · Changing the ingredients, “sameness of traces to bisimulation”
  - **Problem** · Both terms appear in the card ahead of the later explanation. ‘Computability at higher types’ is also a specialist label, though its card has a usable plain heading. The worked process example supplies the missing distinction only after several cards and the audit table.
  - **Severity** · could
  - **Suggested fix** · In the process card say ‘Two processes may tell the same stories of actions while offering different next moves’. In the higher-types card use the concrete question ‘What can we compute if the input is a callable function?’

- **Location** · Changing the ingredients, “The fourth fixes what a type is”
  - **Problem** · This conflicts with Types and The definition, where steps determine whether a predicate is a type and observation is a separate ingredient. ‘A step never changes a reading’ also needs to say that the term under test changes before the same probe is run.
  - **Severity** · should
  - **Suggested fix** · Say ‘A step in the term under test leaves these probe readings unchanged. That makes predicates defined from these readings into types. Types in general were defined by step invariance.’

- **Location** · Changing the ingredients, “The value of a word is the place where its path ends”
  - **Problem** · The group card and expanded example use ‘value’ for an invariant even though there are no normal forms. ‘The three ingredients are present’ leaves the observation implicit. The cost card also alternates between steps in a particular route and the least number of steps over all routes.
  - **Severity** · should
  - **Suggested fix** · Call the endpoint the group element, or the reading of an observer that counts `a` and `b`. Name the number of swaps so far as this run’s cost and the area between the two drawn paths as the minimum cost.

- **Location** · Changing the ingredients, “a hole is a loop that no agreed equation between runs fills”
  - **Problem** · With arrowheads erased, even stepping out and immediately back makes a round trip. The sentence does not explain cancellation, what filling means, or how several equations can combine. The pentagon appeared more than a section back, unassisted at the associativity card and only later recalled with its rule and picture. ‘Hole’ itself appears in the card before the definition.
  - **Severity** · block
  - **Suggested fix** · Before the card, use the pentagon as the memory device: go down one route and back up the other. Explain that a step followed by its reverse cancels and that an equation lets either route replace the other within a round trip. A hole is a round trip that still cannot be reduced to the empty trip. Keep ‘slot’ for a probe’s blank in nearby copy.

- **Location** · Changing the ingredients, “runs differing only in the order of independent steps”
  - **Problem** · The no-holes argument needs more than swaps: its own example compares a one-step discard with a longer run that first works inside the discarded argument. The main text gives no rule for identifying those runs and leaves the necessary example to the sidenote. ‘The rule overlaps with itself’ also assumes rewriting vocabulary at the decisive comparison.
  - **Severity** · block
  - **Suggested fix** · Explain that when a rule erases an argument, a step inside it has no remaining work after erasure, and when it copies the argument the corresponding work can occur in both copies. Contrast this with `((xy)z)w`, where two ways of matching associativity give genuinely competing routes. State the no-holes inference using paths to the common value.

- **Location** · Changing the ingredients, “in the first thousand interactions no net comes round again”
  - **Problem** · The Nets note and graph readout turn this finite observation into ‘there is no loop, and so no hole’. A nonrepeating forward path alone does not decide a hole in the undirected picture just defined. ‘Any two of them’ also needs common endpoints, and ten interactions refers to completed runs of the example.
  - **Severity** · block
  - **Suggested fix** · Say ‘Every complete run of the left example takes ten interactions. Routes with the same endpoints in this lattice are related by commuting squares.’ For the right, state that the displayed prefix shows growth and no repeat in the sampled run. Leave the question of holes in the full fibre open unless the essay supplies the argument.

- **Location** · Changing the ingredients, “The number of interactions is a behaviour”
  - **Problem** · A number by itself is not a family with invertible transport. Equal lengths for runs with common endpoints does not imply there is no second route, and the note asserts ‘a lap always counts’ just after saying this net has no lap. Nets displays tree loops here, and the shared caption describes SKI rules even when the expanded I-steps contain S- and K-steps.
  - **Severity** · block
  - **Suggested fix** · Put ‘Tree counter example’ above those panels in Nets. Give a separate net example with an integer at each net, adding one forward and subtracting one backward, and explain that both routes around a commuting square add two. Name only the copying S-step as the increment in Trees.

- **Location** · Changing the ingredients, “The loop ω ω can carry a counter because it has no exit”
  - **Problem** · The absence of an exit alone does not show a counter survives the agreed equations, and ‘no exit’ can mean no step leaves the displayed cycle, contrary to the earlier sidenote. The later three-loop recap treats the full hole as settled while the Mechanized footer states a narrower result.
  - **Severity** · block
  - **Suggested fix** · Distinguish ‘no run reaches a value’ from remaining inside the drawn cycle. Keep the local `+1` example, explain what the rightmost-branch result establishes on K-free terms, and label the full hole claim at the point of use with its actual support.

- **Location** · Changing the ingredients, “a family whose fibre is the integers”
  - **Problem** · Here ‘fibre’ means evidence over one term, after it has meant a component of terms throughout. The universal-cover analogy supplies no help to readers who do not already know it.
  - **Severity** · could
  - **Suggested fix** · Say ‘This is the circle-cover example in homotopy type theory: the possible evidence values at the starting point are the integers, and a lap sends n to n + 1.’

## Summary

- **Location** · Summary, “the fundamental lemma for K”
  - **Problem** · After several sections, the summary names the lemma without the earlier figure’s memory cue. ‘The useful ones’ further demotes step-defined types that the essay deliberately introduced.
  - **Severity** · should
  - **Suggested fix** · Recall the single move: ‘Since K u v steps to u, membership of u carries back to K u v.’ Say that probes give one way to define types.
