# R1 G — Figures and interaction

Reviewed the served copy of `7626ff8` in Chromium at 1280 and 390 CSS px, in all three calculus modes and both color schemes.  
Exercised the figure controls and all ten calculus switches, checked radio and SVG focus with the keyboard, and emulated the reduced-motion CSS and JavaScript branches in an in-page copy.  
The Node suite passed all 207 checks. The figures’ main visual patterns hold up, but the net bench and fibre graph contradict their own readouts, and the running figure can hide keyboard focus.  
Two screenshots document the net bench on a phone and the net graph on desktop.

## Atoms and probes

- **Location** “Rows with the same readings in every column cannot be told apart by these four probes.”  
  **Problem** In Nets, `K I` and `K (S K K)` share a point, but `[ ] x y` displays `y 9` and `y 10`. A reader can distinguish the rows by the visible data. The caption never says that the cost is excluded from the reading used to group rows.  
  **Severity** block  
  **Suggested fix** Label the count as run metadata and say “Point groups rows by returned answers. If the probe also returns interaction count, it distinguishes these two rows.” [Phone screenshot](G-shots/net-bench-390.png)

- **Location** “The last column numbers the points.”  
  **Problem** At 390 px the four-probe table is 388 px wide in Trees and 442 px in Nets, inside a 354 px column. The Point column falls offscreen. The unbreakable triage formula also expands the whole page to 492 px, so panning takes the row labels offscreen.  
  **Severity** should  
  **Suggested fix** Wrap the formula at application boundaries. Keep the table within the figure with a compact layout or a labeled, keyboard-scrollable wrapper with persistent row labels. Change “Six terms under three probes” to “Six terms under four probes” when triage is present. [Phone screenshot](G-shots/net-bench-390.png)

## Running a term

- **Location** “outermost redex first”  
  **Problem** The loop ignores the Order selector. Start from `I ω (I ω)` and scrub to time 1. Both orders show `I ω ω` in Combinators, though outermost first gives `ω (I ω)`. Both show `K ω (△ω) (I ω)` in Trees, though arguments first gives `I ω (K ω (△ω))`. The animation silently substitutes its curated cycle for the selected strategy.  
  **Severity** block  
  **Suggested fix** For loop terms, replace Order with a visible “Shown cycle” label, or include the alternative reducts and follow the selected strategy.

- **Location** “Select any box to run that term.”  
  **Problem** In One step and One run, the hidden SVG boxes remain focusable. In Combinators, tabbing from Time in the initial One step view reaches the visible `S K K a` box, then the invisible `K a (I b)` box at opacity 0. Its focus ring vanishes with it, and the hidden button can still change the run.  
  **Severity** block  
  **Suggested fix** Remove hidden boxes from keyboard, pointer and accessibility navigation as the view changes. Keep the Term selector available for choosing any term and retain focus on a visible control if its current target disappears.

- **Location** “Each box is a term and each arrow is a step.”  
  **Problem** The Nets caption still offers box selection, while All the states draws dots with unheaded edges and has no node controls. Its SVG label still says “Fourteen terms,” even when the diagram is one net or a lattice of nets. The same fixed SKI descriptions recur in the Types and fibre figures, including the claimed three-node cycle in the net graph.  
  **Severity** should  
  **Suggested fix** Give each mode its own visible caption and accessible description. In Nets, say “Each dot is a net. Follow the green path with Time, or choose another starting term under Term.” Identify which way time runs at each layout width, or draw arrowheads.

## Three equalities

- **Location** “Each equality is coarser than the one before it.”  
  **Problem** In Trees and Nets with the added rule, Same after running has three points and Same under every probe has five. The latter splits the merged identities. The readout reports the clash correctly, while the caption still asserts the opposite.  
  **Severity** block  
  **Suggested fix** Make the caption conditional. With the rule active in Trees or Nets, say “The added rule merges three terms that probes still distinguish.”

## Types

- **Location** “Close it”  
  **Problem** After closing a leaking predicate, the newly shaded boxes still expose `aria-pressed=false`. Clicking one of those boxes starts a custom predicate from the pre-closure selection, so the clicked box stays shaded while the other added boxes disappear. The visual state and the next action disagree.  
  **Severity** should  
  **Suggested fix** Reflect the displayed membership in `aria-pressed`. Seed hand edits from the displayed closed set before toggling the selected term.

- **Location** “A red arrow is a leak”  
  **Problem** The perpetual leak pulse drops the red stroke to 35% opacity. At the trough it has about 1.8:1 contrast against the paper in light mode and 1.9:1 in dark mode. The arrow that carries the result becomes harder to see than the ordinary green arrows.  
  **Severity** should  
  **Suggested fix** Use a steady red stroke and the existing heavier weight, or keep at least 3:1 contrast throughout a brief cue.

## What a type cannot see

- **Location** “the net of ω ω”  
  **Problem** In Nets, the detached-work box shows statistics for the whole `K a (ω ω)` net. Its display already counts work toward producing `a`, before the eraser is detached, under a label that attributes the numbers to `ω ω` alone.  
  **Severity** should  
  **Suggested fix** Label the numbers “Whole net” and mark when the result port first reads `a`. If the box is meant to show just the detached work, start that readout at detachment and count that component.

- **Location** “The solid marker runs the argument first and never arrives.”  
  **Problem** Reduced-motion mode still moves the net exit marker around a ring and repeatedly moves the fibre markers, including through intermediate positions. Net dots and lattice fills also keep CSS transitions. The normal-motion diagrams start moving on view and offer no way to stop the repeating motion.  
  **Severity** should  
  **Suggested fix** Offer a static initial view and a pause control for repeating runs. Under reduced motion, use discrete labeled states without automatic cycling or SVG transitions.

## Changing the ingredients

- **Location** “there is no loop, and so no hole.”  
  **Problem** The Nets “A graph” view forgets direction and then denies the loops formed by its own commuting squares. After two interactions of `ω ω`, two distinct next interactions can be swapped to reach the same net after four. They form a round trip in the undirected graph. The depth-five drawing and a thousand steps of one strategy cannot establish the absence of holes in the full fibre.  
  **Severity** block  
  **Suggested fix** Say “The first five layers shown contain commuting squares. Each fills the round trip made by swapping two interactions.” Distinguish these round trips from a directed run returning to the same net. Avoid claiming the full fibre is hole-free without a separate argument. [Desktop screenshot](G-shots/net-fibre-graph-1280.png)

- **Location** “The counter is advanced by one at each use of the S-rule” and “there is no second route for it to disagree with.”  
  **Problem** In Trees and in the tree demonstration shown under Nets, only the root S-step advances the counter. Two other S-steps leave it unchanged. The net note then says there is no second route, although `K a (ω ω)` already starts with two distinct active pairs, and firing them in either order reaches the same net.  
  **Severity** block  
  **Suggested fix** Give the tree panel its own caption that names the root S-step, and label the panel “Tree calculus” above its controls in Nets. In the net note say “Different orders can reach the same net. Each takes the same number of interactions.”
