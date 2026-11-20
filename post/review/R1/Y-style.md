This pass covers the prose, sidenotes, captions, and tree/net notes at `7626ff8`.
The clearest cuts are the opening itinerary and the repeated inventory of Lean results.
The switch notes and card-sort table read most like the body when they name the term, the operation, and the result directly.
The lists of equalities, presentation parts, and tree shapes carry information and should stay.

## Atoms and Probes — opening and switch legend

- **Location** — “Computation is what a type forgets.”  
  **Problem** — The standalone tagline makes a broad claim that outruns the essay’s account of what a predicate records.  
  **Severity** — should  
  **Suggested fix** — “A type can record where a term ends up. The run can still matter.”

- **Location** — “A typed program can be given two accounts.” / “A good part of the theory of programming languages” / “Once they are separated, a third thing can be seen between them”  
  **Problem** — The passive opening, sweeping disciplinary claim, and staged reveal delay the distinction. The “still in draft” aside also starts a series of status notices.  
  **Severity** — should  
  **Suggested fix** — Open with “Typing rules say how to build a term of a given type. A semantic type tests the term’s behaviour.” Then use “The same distinction applies to terms. Atoms make up the text, probes test a term, and steps run it.” Give publication and proof status in the closing material.

- **Location** — “It settles which equalities” / “destroys abstraction” / “The essay goes in this order.”  
  **Problem** — The preview overstates what the account settles and what code inspection destroys. The itinerary then repeats the headings and uses a chain of “first,” “then,” and “follows” signposts.  
  **Severity** — should  
  **Suggested fix** — Keep a concrete preview, such as “A type checker can decide some equalities by running terms. Code inspection can distinguish terms that ordinary application treats alike.” Delete the itinerary.

- **Location** — “Ochre is for descriptions:” / “Blue is for observation:”  
  **Problem** — The repeated colon turns and the blue three-part list make readers decode a key that the next line already displays.  
  **Severity** — could  
  **Suggested fix** — Keep the swatches. Add “Red marks a leak or a clash. A filled green button starts a run” if those two conventions need prose.

- **Location** — Tree switch legend, “has one constant, the leaf △, and five rules:” / “look at the shape of the third argument:”  
  **Problem** — The nested colon lists put five formulas and their explanation in one sentence. The formula inventory reads like a specification embedded in the introduction.  
  **Severity** — should  
  **Suggested fix** — “Tree calculus starts with one constant, the leaf `△`. It has a K-rule and an S-rule.” Set the two formulas together. Then give the three triage rules on separate lines under “Triage chooses a rule by the shape of the third argument.” Keep the abbreviations together as a legend.

- **Location** — Net switch legend, “A term is compiled to a net of agents by the eager table” / “fifteen rules: agents for” / “A net is named by the term read back”  
  **Problem** — Two passives and a colon list obscure what the reader sees. The list mixes the count of rules with kinds of agents.  
  **Severity** — should  
  **Suggested fix** — “The eager table in tree-semantics compiles a term to a net. It has fifteen interaction rules. Nets use agents for leaf, stem and fork, as well as for application, triage, copying and erasure. A step acts on two agents joined at their principal ports. The figures label each net with the term at its result port. A variable supplied by a probe appears as a free wire.”

## Two accounts of a typed program

- **Location** — “take from it one thing:” / “Read: under the assumptions” / “The statement is established by a derivation”  
  **Problem** — The invitation to skip the section sets up a reveal. The figure then switches to a passive, textbook register that makes the derivation harder to follow.  
  **Severity** — could  
  **Suggested fix** — Open with “Typing rules describe how to build a term. Semantic tests describe how to use it.” In the figure use “Under assumptions Γ, term `t` has type `A`. Build the derivation with one rule per term form, then reason by induction on the derivation.”

- **Location** — “The set is a predicate on terms.” / “The next section defines both words.”  
  **Problem** — The figure restates its membership explanation, and the paragraph closes with a signpost after it has already introduced both words.  
  **Severity** — could  
  **Suggested fix** — In the figure use “A term belongs to ⟦A⟧ if it passes the tests for A.” Keep the arrow-type example. End the section with “Probes test how a term behaves when used.”

## Atoms and probes

- **Location** — “a tree of atoms and nothing else” / “it is the black-box view” / “under one restriction: it may read only what it supplied.”  
  **Problem** — The white-box/black-box tags follow definitions that already tell readers what to look at. The restriction is the substantive claim and need not arrive as a reveal.  
  **Severity** — could  
  **Suggested fix** — “A term is a tree of atoms. A probe supplies a context with a hole, such as `[ ] x y). Put the term in the hole and run it. The probe can read the outcome only if it contains just the variables the probe supplied.”

- **Location** — “the three contexts are enough:” / “run that experiment:” / “the reading lands in the cell.” / “The last column numbers the points:”  
  **Problem** — The prose stages three explanations with colons, and the caption narrates a routine UI action as a three-beat sequence.  
  **Severity** — could  
  **Suggested fix** — “For these six terms, agreement in the table implies agreement under every probe.” In the caption use “Select a cell to watch the term run in that probe. Rows with identical readings share a point number in the last column.”

- **Location** — Tree bench note, “a fourth probe is added, the triage probe” / “Its outer part asks that branch’s shape:” / “tells them apart too: in tree calculus”  
  **Problem** — The note puts the row list, passive setup, nested formula, and notation definition in one long sentence. Two more reveal clauses obscure the two separate experiments.  
  **Severity** — should  
  **Suggested fix** — “The table uses `S K (△K)` in place of `S K S` and adds a fourth probe. Write `triage(a, b, c)` for `△(△ a b)c`.” Set the probe formula on its own line. Follow with “The inner test takes the right branch of the top fork. The outer test returns `x` for a leaf, `y` for a stem of a leaf, or `z` for a stem of a stem. This separates the three identities. The table still groups `K I` and `K (S K K)`. First apply each to `x` and then use the triage probe to separate them. The six terms are pairwise distinct under probes.”

- **Location** — Net bench note, “each experiment is compiled to a net and run by interactions” / “commute: any two runs between the same nets have the same length.”  
  **Problem** — The passive setup and colon repeat the count claim. The note can state what is counted and why the count is stable in the same terms as the caption.  
  **Severity** — could  
  **Suggested fix** — “The figure compiles each experiment to a net. Each cell shows the tree-calculus reading and the number of interactions. Interactions commute, so runs between the same two nets have the same length.”

- **Location** — “The syntax is the same in both readings. What differs is the question asked of it:” / “An atom, then, is a part, and a probe is an experiment.”  
  **Problem** — The first passage recaps the worked example and repeats the two questions in the table. The last paragraph restates the opening distinctions after the section has applied them.  
  **Severity** — could  
  **Suggested fix** — Keep the two readings of `S K K x`. End that paragraph after “used on `S K K`.” Delete the closing recap.

## Running a term

- **Location** — “The framework’s word for a run is computation.” / “In this calculus that always happens:”  
  **Problem** — Naming the term in a separate announcement slows the definition. “That always happens” briefly sounds like every run reaches the example’s value.  
  **Severity** — could  
  **Suggested fix** — “A run, or computation, is a sequence of steps.” Then use “Combinatory logic is confluent. Two runs from the same term can be continued until they meet.”

- **Location** — “The figure shows running from four distances.” / “One stage back, the whole run of that term is shown.”  
  **Problem** — The setup narrates the four controls before the reader sees them, using passives to do work the labels already do.  
  **Severity** — could  
  **Suggested fix** — “Choose a term and an evaluation order. The figure can show its next step, its whole run, the surrounding terms, or just the values.”

- **Location** — Tree note, “the same situations are written in trees” / “The loop ω ω has five:” and net note, “Two interactions that can both fire can be fired”  
  **Problem** — “Situations” and “has five” leave readers to supply the nouns. The net note repeats “fire” where the order is the point.  
  **Severity** — could  
  **Suggested fix** — “This view uses tree terms and shows the intermediate steps. The S-rule copies `ω`, then each `I ω` takes two steps, left first. The cycle has five terms.” In the net note use “If two interactions are available, either order reaches the same net. The two routes form a square.”

- **Location** — “The last view is the classical account of what a program means.” / “Nothing in that account is false.” / “takes the whole picture as its object of study.”  
  **Problem** — The blanket endorsement and broad historical framing sound more sweeping than the concrete figure warrants.  
  **Severity** — should  
  **Suggested fix** — “The last view shows the account based on values. Each program with a value sits at that value’s point. The other views also show the steps that connect terms.” Keep the Scott and Strachey note on the value-based account.

## Three equalities

- **Location** — “has three kinds of mark:” / “The line is another matter.” / “they take the colour of what decides the equality:”  
  **Problem** — The introduction repeats that the boxes and arrows are fixed before an abrupt turn to the line. The caption repeats the opening colour key. The three equalities themselves need the list.  
  **Severity** — could  
  **Suggested fix** — “The rules fix the arrows between the terms. The points below show which terms count as equal.” In the caption use “Switch equalities to move the points while the boxes stay fixed.”

- **Location** — “It is the equality that atoms give.” / “It is the only one of the three defined by running.” / “It is the equality that probes give” / “Sameness after running implies sameness under probes:”  
  **Problem** — The definitions repeat their labels and the next paragraph paraphrases its opening implication after a colon.  
  **Severity** — could  
  **Suggested fix** — Keep one defining sentence per equality and retain the links to “definitional” and “contextual or observational.” Start the proof with “Terms joined by steps agree under every probe. A step inside a term is still available when the term sits in the probe’s context.”

- **Location** — Tree note, “therefore unsound here:” / “Something that only a probe could find out is now found by running.”  
  **Problem** — The note delays the reason until after the verdict. The body closes with a passive reprise of the newly merged points.  
  **Severity** — could  
  **Suggested fix** — In the note use “Tree probes distinguish terms that `S K y → I` would join, so the figure draws those steps in red.” End the body paragraph after the sentence about the three points merging.

## Types

- **Location** — “A predicate of this kind will be said to leak.” / “a predicate that does not leak:” / “it is slightly wider: a behaviour may attach evidence”  
  **Problem** — A passive naming formula and successive staged glosses get between the example and the definitions.  
  **Severity** — could  
  **Suggested fix** — “When a step changes whether a term satisfies a predicate, the predicate leaks. A type has the same answer at both ends of every step. A behaviour can attach evidence to a term as well as give a yes-or-no answer.”

- **Location** — “It is simpler to state than those and is not the same as any of them, but it does the part of their work”  
  **Problem** — The comparison stacks a claim of simplicity and two qualifications around the precise claim that the proof needs.  
  **Severity** — should  
  **Suggested fix** — “The types here are closed under steps in both directions. The fundamental lemma below uses closure under backward steps.” Keep the reducibility-candidate example to show how the conditions differ.

- **Location** — Caption, “A red arrow is a leak:” / “The shading takes the colour of what defines the predicate:” and tree note, “That is possible because the probes of tree calculus read code.”  
  **Problem** — The caption repeats the three-colour key through another colon. The note ends by restating what the preceding example already demonstrated.  
  **Severity** — could  
  **Suggested fix** — “A red arrow joins a shaded box to an unshaded one. Select a box to start your own predicate.” In the note use “In tree calculus, a probe can run a term and use a tree program to compare its value with `I`.”

- **Location** — “Two predicates in the list should be compared.” / “Let ⟦A⟧ and ⟦B⟧ be any two types” / “The claim is that K satisfies it.”  
  **Problem** — The signpost delays the examples. The long proof setup embeds a recap and an explanation after a colon, then announces its claim in a separate beat.  
  **Severity** — should  
  **Suggested fix** — Start directly with “‘Runs to `I`’ shades exactly one fibre.” In the proof use “Let ⟦A⟧ and ⟦B⟧ be types. The probe for ⟦A → B → A⟧ tests whether `t u v` belongs to ⟦A⟧ for every `u` in ⟦A⟧ and `v` in ⟦B⟧. To see why `K` passes, take such a `u` and `v`.”

- **Location** — Tree note, “the argument is the same:” / net note, “the term is read through its compilation.” / “The argument uses each notion once.”  
  **Problem** — The two notes announce their method before giving the step or result. The body’s concluding triple and final “This is the sense” sentence restate the proof.  
  **Severity** — could  
  **Suggested fix** — In the tree note use “Here `K` is `△△`. The K-rule takes `△△ u v` to `u`.” Keep the claims about `S` and triage. Start the net note with “After three interactions the net of `△△ u v` reads `u` at its result port.” Condense the body recap to “The K-step carries membership in ⟦A⟧ back from `u` to the term the probe tests, `K u v`.”

## The definition

- **Location** — “The framework’s definition can now be given in familiar words.” / “The first is” / “That is one choice among several, and two later sections change it.”  
  **Problem** — Introductory signposting and ordinal staging delay the definition. The three items are needed, but three separate reveal sentences are not.  
  **Severity** — could  
  **Suggested fix** — “A presentation consists of descriptions built from atoms, steps between descriptions, and an observation. An observation gives a verdict for each pair of a description and an observer.” Keep the probe example and remove the preview of later sections.

- **Location** — “One statement in the definition is more exact than the table.” / “Suppose there is evidence for t, and suppose t steps to u.” / “The other half says” / “In the language of category theory:”  
  **Problem** — The opening leaves the statement unnamed, then repeats the transport condition twice. The category-theory sidenote follows its colon with three results in one sentence.  
  **Severity** — could  
  **Suggested fix** — “If `t` steps to `u`, a behaviour carries evidence across that step in exactly one way in either direction. Subject reduction and subject expansion supply existence. A behaviour also requires uniqueness.” In the note use “Take descriptions as objects and runs as maps. A family is a functor to sets. The steps generate an orthogonal factorization system on families. A behaviour has unique lifting against each step, so it sends each step to a bijection.”

- **Location** — “For evidence with more content it can arise, and the next section shows where.”  
  **Problem** — The transition announces a future example instead of stating the open question plainly.  
  **Severity** — could  
  **Suggested fix** — “Two runs can carry a proof or a number to different results.”

## What a type cannot see

- **Location** — “Three things about the inside matter to a designer:” / “Length was seen” / “The other two are drawn below.”  
  **Problem** — The numbered setup and backward and forward signposts make this sound like a syllabus. Keep the three differences because each has a worked example.  
  **Severity** — could  
  **Suggested fix** — “Inside one fibre, runs can take different numbers of steps. Two routes can carry evidence differently, and the evaluation order can determine whether the run reaches a value. For instance, `K a (I b)` can reach `a` in one step or in two.”

- **Location** — Tree note, “The pentagon is not drawn in combinatory logic, and it does not change.” / net note, “So the answer is there and never changes, yet the run never ends”  
  **Problem** — The tree note repeats the five-term cycle and exits already in the caption, then explains the static panel twice over. The net note uses a dramatic restatement of the result port and eraser.  
  **Severity** — could  
  **Suggested fix** — For tree mode, retain the cycle’s Lean mark with the tree caption and use “The left panel still uses the bracketing rule” if orientation is needed. For net mode use “The result port reads `a` after three interactions. The eraser waits on `ω ω` in every order, so the eager net keeps running with the same reading. The lazy table suspends the argument and finishes in 27 interactions.”

- **Location** — “the question is the one that the definition left open at the end of the last section:” / “For richer evidence it need not”  
  **Problem** — A retrospective signpost delays the point. “Richer” characterizes the evidence without showing what can change.  
  **Severity** — could  
  **Suggested fix** — “Two routes can carry evidence to different results. Predicates give the same yes-or-no answer either way. Mac Lane’s pentagon axiom counts the two routes as one for associativity.”

## When probes can read atoms

- **Location** — “could read only what they supplied:” / tree note, “No checkbox is needed, because the calculus’s own triage does the reading:” / “Tree calculus needs no checkbox.”  
  **Problem** — The first colon restates the restriction. The checkbox explanation then appears in the note and again in the new paragraph. The final sentence of the note obscures the equivalence behind “give sameness.”  
  **Severity** — should  
  **Suggested fix** — Begin “So far a probe could read an outcome only if it contained the variables the probe supplied.” In the note use “The box stays ticked in tree calculus. Triage separates `I`, `S K K` and `S K (△K)`.” Keep the qualified equivalence in the body once, with its Lean link.

- **Location** — “falls back to sameness after running, at least for terms that have a value.” / “It does not fall back to sameness of text.” / “In combinatory logic no probe can do this:”  
  **Problem** — “Falls back” plus “at least” hides a precise scope, and the next sentence introduces a contrast that `I a` and `a` already demonstrate. The new tree paragraph puts two large encodings before their familiar names and stages the comparison after a colon.  
  **Severity** — should  
  **Suggested fix** — “For terms with a value, code-reading probes give the same equality as running. For example, `I a` and `a` still share a point. In tree calculus, `S K △` and `S K K` both return their argument. Their normal forms have different right branches. A probe returns `x` for the leaf and `y` for the stem. In combinatory logic `S K y` and `I` agree under every probe for all `y`.” Give the expanded tree syntax after the names if needed. Keep the generalization and its hypotheses with the result they qualify.

- **Location** — “In such a calculus programs are data.” / “What is given up is abstraction.” / “no two different normal forms can be exchanged”  
  **Problem** — Two slogan-like beats make the loss sound unrestricted. The final clause repeats the preceding detection claim.  
  **Severity** — should  
  **Suggested fix** — “A probe that reads code can distinguish any two different normal forms. Replacing a function by a different normal form can therefore change a probe’s answer.”

- **Location** — “The lambda calculus is at the opposite setting.” / “There application is the only probe, a function is known only by its use, and sameness under probes is much coarser” / “Tree calculus reaches the same place by another road”  
  **Problem** — A rhetorical triple repeats the application point, and the road metaphor restates the mechanism just illustrated.  
  **Severity** — could  
  **Suggested fix** — “In the lambda calculus, application probes can treat terms in different fibres as equal. The checkbox changes what an observer may read. In tree calculus, the triage rules let its own contexts inspect code.”

## Changing the ingredients

- **Location** — “A presentation, which is the framework’s name for a calculus as given by its definition” / “To these must be added one decision” / “And the essay has mostly kept the line” / “Its descriptions are finite:”  
  **Problem** — The nominalized redefinition and the passive reveal repeat the previous definition. The staccato three-sentence setup makes the later four-column sorting harder to anticipate.  
  **Severity** — could  
  **Suggested fix** — “The examples so far use one-way steps and probes that supply arguments and read answers. Most figures also show a line with one point per fibre. We can vary what the steps and probes do and how much each figure keeps.” In the next paragraph use “A Turing machine’s description is finite. It records the tape, the head position and the state. Each step makes one move.”

- **Location** — “At this setting something remarkable was found.” / “two things about it should be noticed.” / “A number has to be written down in each of them”  
  **Problem** — A dramatic opening, a passive numbered signpost, and a sentence over 40 words dilute the specific result. The paragraph’s closing sentence states the role of observation again.  
  **Severity** — should  
  **Suggested fix** — “Church, Kleene and Turing proposed different calculi in the 1930s. These calculi compute the same partial recursive functions.” Then use “The calculi can still differ in the cost and identity of runs. To compare a Turing machine and a combinatory term, encode the same number on the tape and in the term. Compare their answers using the corresponding readings.” End with the concrete comparison.

- **Location** — “Numbers in, numbers out, and only the line kept” / “the cost belongs to the term and not to the run.” / “Programs become data, and abstraction is lost.” / “The value of a word is a group element, the cost of a run is an area, and whether two words share a point can be undecidable.”  
  **Problem** — The baseline title uses slogan rhythm. The cost card repeats its result as an antithesis, the code card repeats the abstraction slogan, and the group card packs three distinct claims into one beat.  
  **Severity** — could  
  **Suggested fix** — Title the baseline “Numeric probes with one point per partial function.” For nets use “Every run of an interaction net to completion takes the same number of steps.” For code use “A program can distinguish different normal forms by inspecting their code.” For groups use “A word represents a group element. Area measures the cost of a run. For some groups, no procedure decides whether two words represent the same element.”

- **Location** — “What the framework adds is the heading:” / “none of it has been checked by referees” / “the central facts have also been mechanized:”  
  **Problem** — The reveal presents the framework’s contribution indirectly. The long proof inventory duplicates the later table, and the status qualifications crowd out the distinction between the cards and their interpretation.  
  **Severity** — should  
  **Suggested fix** — “The cards use the same presentation framework with different choices of steps, observation or what to keep.” Keep the citations. Give the Lean and hand-argument statuses once in “Mechanized,” including which links between the cards and the framework remain to be argued.

- **Location** — “Each property does some work.” / “The third is the whole gap” / table, “The same: the probe sees direction” / “None of the four; there are more probes”  
  **Problem** — The paragraph announces and then numbers its explanations. “The whole gap” overstates the claim in a section whose code result is qualified to terms with a value. The table shifts from concrete operations to a cross-row shorthand.  
  **Severity** — should  
  **Suggested fix** — Tie the explanations to their subjects. “Step-invariant readings give the implication from running to probes. Probes built from terms can be composed with contexts. Reading code can distinguish the identities. With a reading or no reading, a probe can define a yes-or-no predicate.” In the cost row use “A step can change the reported cost.” In the process row use “A probe can see an action as it happens.” In the higher-type row use “Keeps all four properties and accepts more probes.” Rename the second column “Change to the probes.”

- **Location** — “Two of the cards are drawn larger here, because they are the furthest from the calculus of this essay.” / “The second is the card on groups.” / “exchange two letters:”  
  **Problem** — The unexplained ranking and ordinal transition announce examples that can start with a concrete action. The grid caption restates the swap as a reveal.  
  **Severity** — could  
  **Suggested fix** — Begin “A trace lists the actions a run shows.” Introduce the next example with “Take two generators, `a` and `b`, and the relation `ab = ba`.” In the caption use “Select a green corner or use the green buttons to swap two letters. The path moves across one square, which the figure shades or clears.”

- **Location** — “Nothing in this picture resembles a machine.” / “there is no input, no output and no order of evaluation.” / “and so is cost:” / “The last card, on keeping the fibres, needs explaining”  
  **Problem** — The rhetorical opening, negative triple, and cost reveal dramatize a concrete contrast. The next paragraph opens by announcing an explanation.  
  **Severity** — could  
  **Suggested fix** — “A relation can move the path across a square in either direction. The shortest route between two words has one step per square between their paths.” For the next paragraph, start “A single point can represent the whole fibre. Keep the edges and the fibre becomes a graph. Keep the arrowheads as well and the graph records the direction of steps.”

- **Location** — Net fibre note, “there is nothing to count as one beyond the swapping of two interactions.” / “it does not loop but grows” / “There is no loop for a hole to be in.”  
  **Problem** — The first claim is less direct than the square description. The contrast and final sentence turn a bounded check into a categorical conclusion, then repeat it.  
  **Severity** — should  
  **Suggested fix** — “The left panel groups reachable nets by interaction count. Swapping two available interactions gives the two sides of a square. Every complete run takes ten interactions. On the right, the net of `ω ω` grows. No state repeats in the first thousand interactions of the run checked.” The design note records the bounded check. State a stronger conclusion only with separate support.

- **Location** — “Evidence, it will be recalled” / “The step from there to the absence of holes” / sidenote, “normal derivation theorem (part I, theorem 3.26):” / “This is why types as predicates serve such calculi well”  
  **Problem** — The recall formula, abstract noun phrase, and long reveal sentence interrupt the proof chain. The interpretive close repeats that the point captures what a predicate can see.  
  **Severity** — should  
  **Suggested fix** — “A family can attach evidence such as a proof or a number to a term. A predicate gives a yes-or-no answer. On a fibre without holes, two runs with the same endpoints carry evidence to the same result. Lévy’s theorem identifies runs to the same value. In Lean, that hypothesis implies that the fibre has no holes. A behaviour on the fibre then amounts to evidence about the value.” In the note make “Project either run along the other. Nothing remains to do at the value” its own explanation. Go directly from the result to the bracketing counterexample.

- **Location** — “the loop ω ω is the smallest example” / “The counter is advanced by one at each use” / tree note, “advances at the use of the S-rule that copies”  
  **Problem** — The superlative needs a specified measure and support. The caption uses a passive, and the tree note can name the single step directly.  
  **Severity** — could  
  **Suggested fix** — “The loop `ω ω` is one example.” Caption it with “The S-rule adds one to the counter. The unmarked I-steps leave it alone.” In tree mode use “Only the step `ω ω → I ω (I ω)` advances the counter. The S-steps inside the expanded I-steps leave it alone.”

- **Location** — Net counter note, “Nothing is discarded either:” / “So a lap always counts.” / “there is no second route for it to disagree with.”  
  **Problem** — The note first says there is no loop, then gives a one-line verdict about laps. It implies there is no second route after earlier notes showed multiple orders with equal counts.  
  **Severity** — should  
  **Suggested fix** — “This panel keeps the tree-calculus loop. In the eager net of `K a (ω ω)`, the eraser waits on `ω ω`. Two runs between the same nets take the same number of interactions, so an interaction count can carry evidence consistently along either route.”

- **Location** — “though it is not a type in the sense of this essay, since it is not a predicate.” / “What the counter records is the route.” / “On the right the same counter fails.” / “Among terms without K it is enough to count only”  
  **Problem** — The double qualification and staged closing sentence crowd the actual reason the counter depends on the path. The next paragraph’s long sentence combines the counting rule, its proof status and its consequence.  
  **Severity** — should  
  **Suggested fix** — “On the left, each step carries an integer in exactly one way. After a lap the same term carries a different integer, so the text cannot determine the count.” On the right begin “The two runs to `a` count as one, but the counter gives one result for the run that circles the loop and another for the run that skips it.” Split the extension into “For K-free terms, count S-steps on the rightmost branch. Lean shows that equivalent runs have the same count. Thus no run out of `ω ω` undoes a lap.” Put the status of the extension to terms with `K` in “Mechanized.”

- **Location** — “Readers who know homotopy type theory will recognise” / “The earlier sections showed three loops, and they are three different cases.” / “Where evidence depends on the route” / “It owes its position to three choices:”  
  **Problem** — The analogy is useful, but the appeal to readers, the ordinal recap, and the two standalone conclusions build to a second summary before the actual summary. The triple at the end repeats choices already stated.  
  **Severity** — could  
  **Suggested fix** — “The universal cover of the circle gives the same example in homotopy type theory. One lap adds one to the integer attached to the point.” Then lead with “The pentagon needs an equation to fill it. The K-rule fills the loop in `K a (ω ω)` by discarding its argument. In the unfilled case, the counter records the route.” Leave the recap of the usual notion to the summary.

## Summary

- **Location** — “The useful ones are defined by probes” / “which is why it has been taken for the whole subject” / “Some of them have results that depend on the route taken, and those results are recorded by no value.”  
  **Problem** — “Useful” overstates the role of probe-defined types after the essay exhibits a type no probe defines. “The whole subject” and the closing flourish repeat the preceding section’s grander conclusion.  
  **Severity** — should  
  **Suggested fix** — “A probe can define a type, and the proof for `K` uses a step to carry membership back to the tested term.” For the last paragraph use “With finite local rules, numeric probes, and only the line kept, every universal calculus gives the same partial recursive functions. Keeping the fibres lets us distinguish runs that end at the same value.” Keep the three equalities in the summary because the enumeration is the claim.

## Mechanized and closing note

- **Location** — “The proofs contain no gaps” / “Runs are counted as one when they differ” / “The six terms under three probes: the points in the table are right”  
  **Problem** — The introduction uses a broad assurance where a checkable proof status would match the essay’s register. The table then uses a looser claim than the body’s partition into points.  
  **Severity** — should  
  **Suggested fix** — “The Lean marks and table link to declarations in commit `d58539e`. The proofs use no `sorry`. `AXIOMS.md` lists the standard axioms each proof uses. Lean counts runs modulo the elementary squares listed in the development.” Use “The probes partition the six terms into the three groups shown” as the first row. Leave the comparison with Lévy in the gap list.

- **Location** — Table, “such probes tell I from S K K; I a and a still agree” / “a single run, so counted, to one term” / “Bracketings: without an equation of its own” / “The counter on ω ω: one lap adds one”  
  **Problem** — The table alternates between full sentences and colon headlines. The code row makes three claims in one breath, and “so counted” sends readers back to decode how runs are identified.  
  **Severity** — could  
  **Suggested fix** — Put the three code claims on separate lines in the cell with their declaration names. Use “If every term has one run up to the stated equations to a common term, the fibre has no holes. A behaviour on that fibre is evidence about the common term.” For bracketings use “Without an equation identifying the two bracketing routes, they can carry evidence to different results.” Use “Each lap of `ω ω` adds one to the counter.”

- **Location** — “Not mechanized:” / footer, “Part of it has since been mechanized in the Lean proof assistant, with the Mathlib library:” / “The section before this note lists each mechanized claim”  
  **Problem** — The gap list is one sentence over 40 words, and the footer repeats both inventories and signs back to the table. Readers have to reconcile status across three places.  
  **Severity** — should  
  **Suggested fix** — Keep one compact gap list here, with separate entries for cited results, hand arguments, and open extensions. Keep the two Lévy questions distinct: identifying runs to a value, and whether the Lean equations give Lévy’s equivalence. In the footer retain the provenance and figure method alone. “The framework began in a design conversation. A browser reducer computes the arrows and probe readings.” Retain hand-selection and layout credit where it describes the figures accurately.
