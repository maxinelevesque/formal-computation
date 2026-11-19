# 15. One essay, three calculi: the calculus switch (design, 2026-11-19)

Maxine's request (2026-11-19): every example and interactive in "Atoms and Probes" gets
its tree-calculus and interaction-net equivalent, selectable by a toggle, as a
demonstration of the whole framework. `tree-semantics` will be made public. Its links are
pinned to `5147cfa` on GitHub; they are broken until it is.

## 15.1 The switch

**One switch.** A segmented control at the top of the essay, repeated as a small sticky
control beside each figure that changes: **Combinatory logic · Tree calculus ·
Interaction nets**.
- It sets one global state, and every figure re-renders.
- The URL hash keeps the choice (`#calc=tree`).
- Default: combinatory logic.

**What changes and what does not.**
- *Changes:* the descriptions, the steps and the probes, which are the three ingredients.
- *Unchanged:* the framework: fibres, the three equalities, types, holes.
- That is the point of the demo. Figures that are not about SKI (the pentagon, groups,
  processes, two calculi) have no switch.

**Prose.**
- The body text stays written for combinatory logic.
- Each figure gets a short, switch-dependent note under its caption,
  `<p class="calc-note" data-calc="tree">`. It says what differs in that calculus, with
  its Lean or citation mark.
- Claims that change truth value (below: ✱) must have such a note.

**Notation for tree calculus.** Write `△` for the leaf, and juxtaposition for
application. Use abbreviations, shown in a fixed legend under the switch:
- `K = △△`;
- `I = △(△K)△` (that is, `S K △`);
- `S x y = △(△x)y`;
- `ω = S I I`.

Then most examples read as in SKI, and the extra intermediate terms are visible.

**Interaction nets.**
- A term is compiled to a net by the eager table of `tree-semantics`
  (`TreeCalculus/IxTree.lean`, `eagerTable`).
  - Constructors: L, S, F.
  - Consumers:
    - A, application;
    - T and Sel, triage;
    - D, duplication;
    - E, erasure.
  - Fifteen rules.
- A state is a net and a step is one interaction.
- States are labelled by the read-back of the result port, plus the number of agents.
  The figure of a single state draws the net itself.
- Variables supplied by a probe are free wires.

## 15.2 Figure by figure

| Figure (id) | Combinatory logic (now) | Tree calculus | Interaction nets |
|---|---|---|---|
| Bench: six terms × three probes (`grid`, `svg-tree`) | `I, S K K, S K S, K I, K (S K K), K`; probes `[ ]`, `[ ] x`, `[ ] x y` | `I, S K K, S K (△K), K I, K (S K K), K`; same three probes **plus a fourth, the triage probe**, which separates the three identities ✱ | same answers as tree; **each cell also shows the number of interactions, which every run shares** ✱ |
| Running from four distances (`svg-hero`; order: outermost / arguments first) | 14 terms, hand layout, 5 fibres incl. the ω ω loop | the same 14 situations in tree terms. Each I-step becomes two steps (S then K), so the bundle has more boxes. Automatic layered layout | one term at a time. The "all steps" view is a lattice of commuting squares, and "order" changes the path but **never its length** ✱ |
| Three equalities; "Add the rule S K y → I" (`svg-base`) | the rule is sound: probes cannot tell S K y from I | **the rule is unsound**: the triage probe separates them, so adding it collapses fibres that probes keep apart ✱ | as tree |
| Types: a predicate and its leaks (`svg-paint`) | predicates over the bundle; "runs to I" is a type no probe defines | the same predicates; **"runs to I" is defined by a probe** (equality of code is a program) ✱ | as tree |
| Fundamental lemma for K (`svg-lemma`) | `K ∈ ⟦A → B → A⟧` | the same, with `K = △△`. Also triage: `△(△ w x) y` respects types when its branches do | as tree, read through compilation |
| Two routes / a loop with exits (`svg-pent`, `svg-exit`) | pentagon: no switch. `K a (ω ω)`: loop with exits | `K a (ω ω)` in tree terms: the same shape, longer loop | **eager net: the answer `a` is at the result port after a few interactions, but the eraser waits on ω ω forever. The run never ends, although the answer never changes** ✱ (a lazy table finishes: 27 interactions) |
| Probes read code (`svg-code`, checkbox) | the checkbox gives probes the power to read code | **the checkbox is always on**: the calculus's own triage does the reading ✱ | as tree |
| Fibre over a value / fibre with no value (`fib-a`, `fib-w`) | `K a (I b)`: two runs counted as one (Lévy); ω ω | the same, with the I-step expanded | **the two runs are one square; every run has the same length; nothing to count as one beyond swapping** ✱ |
| The counter on ω ω, and inside K a (ω ω) (`svg-loop`, `svg-kloop`) | a lap adds one; inside K a (ω ω) a lap counts for nothing | the counter on tree ω ω (S-rule uses on the rightmost branch); absorbed inside K a (ω ω) | **nothing is discarded, so a lap always counts: the interaction count is a behaviour** ✱ |
| Cards (`z1`…) | static | static; the cost card notes nets | static |

## 15.3 Claims to mechanize or cite

**In this repository** (Lean; `Tree/…`, plus abstract results):
1. The tree bench table: the six terms under the three probes, and the triage probe
   separating the identities. *(Extends `Tree.probes_read_code`.)*
2. `S K y` against `I` in tree: for `y ∈ {△, K, △K}`, not the same under probes. So the
   rule `S K y → I` is unsound for tree probes.
3. The tree fundamental lemma for K, and for triage given its branches.
4. The tree ω ω loop (a cycle) and its counter. The counter is absorbed inside
   `K a (ω ω)`.
5. **Abstract nets.** In a calculus whose steps form a one-step diamond in which
   distinct steps commute, all runs between two terms have the same length. So the step
   count is a behaviour, valued in ℕ, and sees no direction.
6. "Runs to I" is probe-definable in tree calculus. This needs an equality program; port
   from `tree-semantics` (`Tree.exists_eq`) or cite it.

**Cited from `tree-semantics`** (links pinned to `5147cfa`):
- `Ix.strong_confluence`, `Steps.unique`, `Steps.equal_lengths`;
- `eager_sound`, `adequate`, `finishes_iff_eval`;
- `exact_cost`, `every_finishing_run`;
- `discarded_divergence`, `fire_commute`, `Run.perm`;
- `Tree.intensional_observation`, `Tree.exists_eq`, `pk1Tree_equiv`,
  `pk1Conv_not_equiv`, `pk1Net_eq_tree`.

**Not to publish:** `docs/interaction-nets/disp-ic.md` (disp's table) without Zya's
agreement.

## 15.4 Build plan

1. **JS calculus modules** (`post/lab/`), tested under Node:
   - `ski.js` (extracted), `tree.js`, `net.js`;
   - one interface: parse, print, redexes with rule labels, contract, outcome test, plug
     probe;
   - for nets also: compile, interactions, read-back, canonical state key, draw.
2. **Generic figure layer:** a calculus argument in place of the SKI functions, and an
   automatic layered layout for bundles without a hand layout.
3. **The switch and the calculus notes**, figure by figure.
4. **Inline** the modules into the single-file essay (it stays one file), and re-run
   `lean-links.py`.
5. **Review round R1** over the result.
