# The calculus layer for "Atoms and Probes"

Three calculi behind one interface, so that every SKI interactive in the essay can be
re-rendered in tree calculus or in interaction nets (design: `notes/15-three-calculi-in-the-essay.md`).
Plain browser scripts (ES5, `var` and `function`), no dependencies. Each attaches to a global
`CALC` and is also a Node module, so they can be inlined into the single-file essay.

| file | global | what |
|---|---|---|
| `ski.js` | `CALC.ski` | combinatory logic, extracted from the essay's reducer |
| `tree.js` | `CALC.tree` | tree calculus, triage presentation, with abbreviations |
| `net.js` | `CALC.net` | interaction nets: the eager table of `tree-semantics` (needs `tree.js` first) |
| `graph.js` | `CALC.graph` | reduction graphs, runs, and an automatic bundle layout, for any of the three |
| `test.js` | | the tests of the modules: `node post/lab/test.js` (about five minutes; no packages) |
| `essay-test.js` | | the essay under a stub DOM: `node post/lab/essay-test.js` (seconds) |
| `stubdom.js` | | the stub DOM: an HTML parser, the selectors and element methods the essay uses, a fake clock |
| `essay-ski-snapshot.json` | | hashes of every figure of the essay before the switch, for `essay-test.js` |
| `essay-reducer.js` | | the essay's SKI reducer before the switch, verbatim, for `test.js` to compare with |
| `demo.html` | | a standalone page: open it in a browser (load order: ski, tree, net, graph) |

## The interface

Each calculus module has

```
id, name
parse(s)                 -> state
print(t, opts)           -> string   opts: html, mark (a redex: its `at`, or a net pair), raw (tree: △ only)
key(t)                   -> string   equal keys = equal states (nets: up to renaming of agents and wires)
redexes(t)               -> [{ at, rule, ... }], outermost first
contract(t, redex)       -> state
step(t, strategy)        -> { t, rule, at } | null
isNormal(t), isOutcome(t)            outcome = normal and written in variables alone
plug(probe, t)           -> state    probe: a list of variable names, or a context with a hole [ ]
run(t, strategy, max)    -> [states]
```

Strategies: `'outer'` (the head redex, then the arguments left to right) and `'inner'`
(arguments first, the essay's `redexInner`); for nets also `'oldest'` (a fixed pair order:
the pair with the oldest agent), `'random'` (pass a generator from `CALC.net.rng(seed)` as
the third argument of `step`/`run`), or any function `(pairs, state) -> pair`.

Terms (`ski`, `tree`) are `{ k: 'a', n }` and `{ k: 'p', f, x }`. A redex position `at` is a
path, a string of `f` (function) and `x` (argument) from the root; the essay used node
identity, which goes wrong when the S-rule shares its third argument (below).

**`ski.js`** behaves as the essay's old reducer (kept in `essay-reducer.js`; the essay now runs on
`ski.js` itself), and the test compares the two. On 414 terms (the essay's fourteen and 400 random ones)
the redexes and rule names agree, arguments-first runs agree, and outermost runs agree on all
the terms the essay shows. Eleven random terms differ in outermost runs, all on a loop of
`S I I (S I I)`: the essay's `contractAt` contracts by node identity, so a redex inside the
shared argument of an S-step is contracted in two places in one step. With sharing removed
after each step, the essay's reducer agrees with `ski.js` on all 414. The essay never shows
such a run (its loop terms are run arguments first), so nothing visible changes.

**`tree.js`** is the five rules of `FormalComputation/Tree/Calculus.lean`, rule labels "the
K-rule", "the S-rule", "triage on a leaf / stem / fork"; `'outer'` is that file's `step`.
Abbreviations are expanded by `parse` and recovered by `print`: `K = △△`, `I = △(△K)△`,
`S x y = △(△x)y` (so `S` must have two arguments), `ω = S I I`, and
`triage(a, b, c) = △(△ a b) c`. Any other name is a variable. `print(t, { raw: true })` gives
the △ form; no space is printed directly after `△` (`△K`, `△(△K)`). Also exported: `leaf, K, I,
S(x, y), omega, triage(a, b, c)` as terms.

**`net.js`** states are nets `{ kind, link, next, loops, steps }`, never mutated.
- `compile(term)`, `compileApp(f, x)` (Lean's `compile f x`), `start(string)`.
- `activePairs(net)` (= `redexes`, nearest the result first), `fire(net, pair)`.
- `readback(net)` gives `{ term, pending, garbage, ok }`; `size(net)`; `key(net)`.
- `layoutNet(net)` gives triangles, ports, wires as cubic curves, free ports, and a `viewBox`.
- `print(net, { size: true })` appends the agent count.

**`graph.js`** has three functions.
- `reductionGraph(calc, terms, { max, closed, maxDepth, label })`: breadth-first search over keys.
  - Each state gets `normal`, `outcome`, `onCycle` (Tarjan), and `fibre`. The fibre is the key of the
    normal form it reaches, `'none'` (no value), or `'open'` (the search stopped before deciding).
  - `closed: true` keeps only the given terms and the steps between them, as the essay's bundle does.
- `runPath(calc, t, strategy, { max })`: stops at a normal form, at a repeated state (`cyc`,
  `cycleStart`), or at the cap.
- `layoutBundle(graph, { width, height, orientation: 'wide' | 'tall', layering, slots, rings })`: the hero figure's conventions.
  - Each fibre sits over its own point of the line, in the order of the given terms, with "no value" last.
  - The normal form is nearest the line, and the other states are layered by their distance to it:
    the shortest (`layering: 'nearest'`, the default) or the longest run to it (`'longest'`).
  - `slots: true`: a step over more than one layer gets a slot in each layer it crosses (Sugiyama's dummy
    nodes), its edge gets `via`, the slots' points, and the rows are ordered by sweeps both ways.
  - `rings: true`: a fibre with no value whose states lie on one loop is drawn as a ring, in the given order,
    clockwise from the top, instead of as a column.
  - Returns nodes `{ x, y, w, label }`, edges (with `via`), fibre points, the line, and a `viewBox` that covers every box.

## Interaction nets: conventions taken from tree-semantics

From `TreeCalculus/IxTree.lean` (`treeSig`, `ruleAL … ruleEF`, `eagerTable`) and
`IxCore.lean` (`fire`), `IxTreeCompile.lean` (`compile`, `compileTm`), `IxTreeRegion.lean`
(`readback`), `IxTreeCost.lean` (`EvalNet`):

- Port 0 is principal and port i+1 is auxiliary i. The auxiliary order is S(child), F(left, right),
  A(arg, res), T(y, z, res), Sel(w, x, y, res), D(out0, out1); L and E have none.
- A rule's boundary lists the left (consumer) agent's auxiliary ports, then the right
  (constructor) agent's. Its right-hand side is transcribed cell for cell. A wire between two
  boundary slots splices the outside ports; slots joined only to one another add to `loops`.
- **Compilation.** A closed tree (△ with at most two arguments, each a closed tree) becomes a
  constructor region, as `ofTree`. Every other application is an A agent, as `Code.app`, so
  `compileApp(f, x)` is exactly `compile f x`. Choices beyond Lean, which has no variables:
  - A variable is a free wire (`$x`); the result is the free wire `@`.
  - A variable used more than once gets a chain of duplicators facing its free wire.
  - `△ x` with x not a closed tree is an application `A(L, x)`, as in `compileTm`.
    `compile(t, { direct: true })` builds a stem directly instead.
- **Read-back** extends Lean's (constructors only). An A agent's result reads as an
  application, T's as `△ u y z`, and Sel's as `△ (△ w x) y z`; these nodes carry `pending: true`
  and the agent id, so `print(net, { html: true })` marks them. A duplicator's output reads as
  what it copies, and a free wire as its variable. Anything else reads `?`. Agents the read-back
  does not reach are counted as `garbage`: erasers and duplicators stuck on a variable, and
  detached work such as the ω ω inside `K a (ω ω)`.
- **Key.** The canonical form is a breadth-first labelling from `@`, then from the variables in
  name order. Each detached component is labelled from its least start; the components are sorted.
  The key includes the loop count.

The test checks the table's coverage (each right-hand-side port once). Its strongest check is
against Lean's cost recursion `EvalNet`: on 300 random closed applications `f x`, the number of
interactions, the value read back, and the absence of garbage all agree with `EvalNet`.

## Results (from `node post/lab/test.js`)

**SKI bench** (outermost; `*` = not read): the essay's table, three points.

| term | `[ ]` | `[ ] x` | `[ ] x y` |
|---|---|---|---|
| `I` | `I`* | `x` (1) | `x y` (1) |
| `S K K` | `S K K`* | `x` (2) | `x y` (2) |
| `S K S` | `S K S`* | `x` (2) | `x y` (2) |
| `K I` | `K I`* | `I`* (1) | `y` (2) |
| `K (S K K)` | `K (S K K)`* | `S K K`* (1) | `y` (3) |
| `K` | `K`* | `K x`* | `x` (1) |

**Tree bench** (outermost steps).
- The fourth probe is `triP` of `FormalComputation/Tree/Essay.lean`, `readShape (extract [ ])`, written
  `triage(x, triage(y, K z, △), △) (triage(K △, K (K △), K I) [ ])`. `extract` takes the right branch of a fork
  (a leaf or a stem goes to `△△△`); `readShape` reads a leaf as `x`, a stem of a leaf as `y`, a stem of a stem
  as `z`. It separates the three identities (`Tree.tree_six_terms`); after `[ ] x` it also reads `x` from
  `K I` and `y` from `K (S K K)` (`triP_x_KI`, `Tree.tree_six_distinct`).
- The older probe `triage(x, K y, △) (triage(△, △, K I) [ ])` reads `x` from `△(△K)△` in 5 steps and `y` from
  `△(△K)K` in 6, as in Lean (`sep_idT`, `sep_idT'`), but `y` from `S K (△K)` too.
- `S K K a →* a` in 2 steps. Tree `ω ω` cycles with period 5 arguments first (the right `I ω` first); the
  Lean cycle (`Tree.omega_cycle`) reduces the left one first, and its five terms have no other step among
  them. `K a (ω ω) → a` outermost, in 1 step.

| term | `[ ]` | `[ ] x` | `[ ] x y` | triage |
|---|---|---|---|---|
| `I` | `I`* | `x` (2) | `x y` (2) | `x` (5) |
| `S K K` | `S K K`* | `x` (2) | `x y` (2) | `y` (6) |
| `S K (△K)` | `S K (△K)`* | `x` (2) | `x y` (2) | `z` (7) |
| `K I` | `K I`* | `I`* (1) | `y` (3) | `I`* (5) |
| `K (S K K)` | `K (S K K)`* | `S K K`* (1) | `y` (3) | `S K K`* (5) |
| `K` | `K`* | `K x`* | `x` (1) | `K △`* (3) |

Points: 1, 2, 3, 4, 4, 5.

**Interactions per bench cell**, eager nets.
- The net read-back equals the tree normal form in every cell.
- The count is the same for every order. For the first three columns this was checked exhaustively over
  the graph of reachable nets up to renaming, with the one-step diamond checked for every pair of active
  pairs in every reachable net. The triage cells reach more than 20,000 nets each, and were checked with
  200 random orders each (all the same length, and the same final net).

| term | `[ ]` | `[ ] x` | `[ ] x y` | triage |
|---|---|---|---|---|
| `I` | 0 | 7 | 7 | 43 |
| `S K K` | 0 | 8 | 8 | 46 |
| `S K (△K)` | 0 | 9 | 9 | 49 |
| `K I` | 0 | 2 | 9 | 50 |
| `K (S K K)` | 0 | 2 | 10 | 52 |
| `K` | 0 | 1 | 3 | 35 |

The probe's applications are A agents, and a variable is a free wire. So `I x` costs 7: A·F,
the S-rule, A·S and A·L (building `K x` and `△x`), A·F, the K-rule, and E·S (erasing `△x`).
`I x y` also costs 7, since `x y` is an application stuck on a variable. Probes with variables leave
erasers or duplicators facing the variable's wire, and the read-back counts them as garbage.

**Eager `K a (ω ω)`.** The result port reads `a` after 3 interactions, and the reading never
changes. After 400 interactions, 304 agents and 11 active pairs remain: the run never ends,
outermost or in random order. (The lazy table of tree-semantics finishes in 27 interactions:
`discarded_divergence`.)

## In the essay

**Inlining.** `python3 -I scripts/inline-calc.py` copies `ski.js`, `tree.js`, `net.js` and `graph.js`, in that
order, into `post/atoms-and-probes.html` between `/* BEGIN CALC (generated from post/lab; do not edit here) */`
and `/* END CALC */`, in a script of their own before the essay's. Running it again changes nothing;
`--check` exits 1 if the essay's copy is stale. Run it after every change here, then `essay-test.js`.

**Combinatory logic is unchanged.** The essay's reducer is now `CALC.ski` (contraction by path). `essay-test.js`
drives every figure through a fixed scenario (every bench cell, every hero term in both orders, every
predicate, every tab and button, with fake time) at 1200 and 400 px, and compares 1118 serialised figures and
readouts with hashes of the essay before the switch (blob `1356f7b`). It checks this on load and again after a
tour of tree calculus and nets. `--diff OLD.html` shows any difference.

**The switch.** One state, `calc` in `ski | tree | net`, kept in the hash (`#calc=tree`, `#calc=net`; none for
combinatory logic). Ten radio groups (the main one under the introduction, and a small one in the controls row
of each of the nine figures that change) are bound to it; a hash change updates them. Figures register a redraw
with `onCalc`. Notes that hold in one calculus are `<p class="calc-note" data-calc="tree">`, shown by the
stylesheet from `html[data-calc]`; one panel text of the loop with exits has `calc-ski` / `calc-only` variants.

| figure | tree calculus | interaction nets |
|---|---|---|
| bench (`grid`, `svg-tree`) | rows `I, S K K, S K (△K), K I, K (S K K), K`; a fourth probe, triage (`triP` of `Tree/Essay.lean`); five points | the same readings; each cell also shows its interaction count, the same for every order; the run line shows the read-back each time it changes |
| running (`svg-hero`) | nineteen terms (below), laid out by `layoutBundle`; the loop is the Lean cycle | one term at a time (the loop left out); "All the states" is the lattice of reachable nets by interactions done; one step draws the net; orders outermost, innermost, random, and the readout gives the common length |
| equalities (`svg-base`) | under probes the points are those of running; the rule `S K y → I` is drawn red and called unsound | as tree |
| reading code (`svg-code`) | the box is ticked and disabled | as tree |
| types (`svg-paint`) | the same predicates on the tree bundle; "runs to I" noted as probe-definable (`Tree.exists_eq`) | as tree |
| lemma (`svg-lemma`) | `K` written `△△`, "the K-rule" | as tree, with a note on compilation |
| loop with exits (`svg-exit`) | `K a (ω ω)` with the five-term loop | the eager net: the result port reads `a` after 3 interactions, a counter of interactions runs to 400 and starts again |
| fibres (`fib-a`, `fib-w`) | `K a (I b)` with the I-step expanded (three routes, of 1, 2 and 3 steps); the five-term loop | the lattice of `K a (I b)`: every run ten interactions; the nets of `ω ω` to depth 5: no loop, so no hole |
| counter (`svg-loop`, `svg-kloop`) | the five-term loop; the counter advances at the S-step at the root, `ω ω → I ω (I ω)`; absorbed inside `K a (ω ω)` | the tree figure, with a note: no loop in the net, nothing discarded, a lap always counts (`Diamond.equal_lengths`) |

**The tree bundle.** The eleven situations of the hand-laid bundle, in its order (`S K K a, K a (I b), K a (K a),
I a, K a b, a, I I, K I a, I, S K K, S K (△K)`), then the intermediate terms that make it closed under one-step
reducts (`K a (△a)`, `K a (K b (△b))`, `K I (△I)`), then the loop of `ω ω` as in `Tree.omega_cycle`: `ω ω → I ω (I ω)
→ K ω (△ω) (I ω) → ω (I ω) → ω (K ω (△ω)) → ω ω`, the left `I ω` first. (Leftmost-outermost does not return to
`ω ω`, and `'inner'` reduces the right one first; the figures follow the Lean cycle whatever the order.) Wide
screens: `layering: 'longest'`, `slots`, `rings`, about 970 units wide. At 820 px and below: `layering: 'nearest'`,
`rings`, and an arrow that would cross a box is bent as little as will clear it.

## Not done here

- Nets of `ω ω` are shown only to a fixed depth. That no net of its outermost run repeats is checked for the
  first thousand interactions only (`test.js`), not proved.
- The exhaustive search is capped at 20,000 nets per cell, so the triage column is checked by random orders.
