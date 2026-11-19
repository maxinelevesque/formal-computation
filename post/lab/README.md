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
| `test.js` | | the tests: `node post/lab/test.js` (about a minute; no packages) |
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

**`ski.js`** behaves as the essay's reducer: the test extracts that reducer from
`atoms-and-probes.html` and compares. On 414 terms (the essay's fourteen and 400 random ones)
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
- `layoutBundle(graph, { width, height, orientation: 'wide' | 'tall' })`: the hero figure's conventions.
  - Each fibre sits over its own point of the line, in the order of the given terms, with "no value" last.
  - The normal form is nearest the line, and the other states are layered by their distance to it.
  - Returns nodes `{ x, y, w, label }`, fibre points, the line, and a `viewBox`.

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
- Triage is the probe `triage(x, K y, △) (triage(△, △, K I) [ ])`, which separates the identities.
- `S K K a →* a` in 2 steps. The probe reads `x` from `△(△K)△` in 5 steps and `y` from `△(△K)K`
  in 6, as in Lean (`sep_idT`, `sep_idT'`).
- Tree `ω ω` cycles with period 5, arguments first. `K a (ω ω) → a` outermost, in 1 step.

| term | `[ ]` | `[ ] x` | `[ ] x y` | triage |
|---|---|---|---|---|
| `I` | `I`* | `x` (2) | `x y` (2) | `x` (5) |
| `S K K` | `S K K`* | `x` (2) | `x y` (2) | `y` (6) |
| `S K (△K)` | `S K (△K)`* | `x` (2) | `x y` (2) | `y` (6) |
| `K I` | `K I`* | `I`* (1) | `y` (3) | `I`* (5) |
| `K (S K K)` | `K (S K K)`* | `S K K`* (1) | `y` (3) | `S K K`* (5) |
| `K` | `K`* | `K x`* | `x` (1) | `y` (3) |

**Interactions per bench cell**, eager nets.
- The net read-back equals the tree normal form in every cell.
- The count is the same for every order. "All orders" was checked exhaustively over the graph of
  reachable nets up to renaming, except where marked with †, which used 200 random orders.
- The one-step diamond held for every pair of active pairs in every reachable net: 539,272 squares
  checked in total.

| term | `[ ]` | `[ ] x` | `[ ] x y` | triage |
|---|---|---|---|---|
| `I` | 0 | 7 | 7 | 30 (5,527 nets) |
| `S K K` | 0 | 8 | 8 | 33 (8,467 nets) |
| `S K (△K)` | 0 | 9 | 9 | 36 (11,995 nets) |
| `K I` | 0 | 2 | 9 | 37 (12,761 nets) |
| `K (S K K)` | 0 | 2 | 10 | 39 † |
| `K` | 0 | 1 | 3 | 24 (1,111 nets) |

The probe's applications are A agents, and a variable is a free wire. So `I x` costs 7: A·F,
the S-rule, A·S and A·L (building `K x` and `△x`), A·F, the K-rule, and E·S (erasing `△x`).
`I x y` also costs 7, since `x y` is an application stuck on a variable. Probes with variables leave
erasers or duplicators facing the variable's wire, and the read-back counts them as garbage.

**Eager `K a (ω ω)`.** The result port reads `a` after 3 interactions, and the reading never
changes. After 400 interactions, 304 agents and 11 active pairs remain: the run never ends,
outermost or in random order. (The lazy table of tree-semantics finishes in 27 interactions:
`discarded_divergence`.)

## Not done here

- The essay is unchanged. Inlining the modules, the switch, and the per-figure notes come later.
- The tree version of the hero bundle (its fourteen situations) is not chosen. `graph.js` lays
  out whatever set of terms is given.
- The exhaustive search is capped at 20,000 nets per cell.
