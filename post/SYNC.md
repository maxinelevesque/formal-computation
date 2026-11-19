# Sync: "Atoms and Probes" ↔ Lean and notes

The essay (`post/atoms-and-probes.html`, received 2026-11-19 at `9d8b555`) is the public
post. `post/post.md` is the technical draft written from the outline. This file records,
claim by claim, what the essay says, its status, and what backs it. Statuses as in
`README.md`. "Lean" means proved, no `sorry`, axioms in `AXIOMS.md`.

## 1. Claims in the essay and what backs them

| § | Claim | Status | Backing |
|---|---|---|---|
| Atoms and probes | `I`, `S K K`, `S K S` agree under every probe; `K I`, `K (S K K)` likewise; the three columns suffice for the six rows | HAND (essay) | Standard simulation argument; not in Lean. Candidate for the probe layer (§4). |
| Running | CL is confluent | CITED | Huet–Lévy, in the essay's note 7 |
| Three equalities | Sameness after running implies sameness under probes | CITED/HAND | Follows from confluence; not in Lean (needs Church–Rosser for CL) |
| Three equalities | `I`, `S K K`, `S K S` lie in different fibres | CITED | Distinct normal forms + confluence. **Text fixed** (§2, E2) |
| Three equalities | `S K y → I` is sound | Lean | `SKI.skRun` |
| Types | A type shades whole fibres | Lean | `SKI.IsType.conv`, `SKI.isType_of_conv` |
| Types | "Close it" gives the least type containing a predicate | Lean | `SKI.isType_close`, `SKI.le_close`, `SKI.close_le` |
| Types | A predicate defined by a probe is a type | Lean | `SKI.isType_arr` |
| Types | Fundamental lemma for K | Lean | `SKI.fundamental_K` (also `fundamental_I`, `fundamental_S`) |
| Types | Comparison with Tait / Girard / biorthogonality | CITED | **Text fixed** (§2, E3): "stronger than those" was false for Girard's CR3 |
| Definition, note 14 | A behaviour is a family sending every step to a bijection; unique lifting against each step | Lean | `beh_iff_map_bijective_co` (covariant, the essay's reading), `beh_iff_M` |
| Definition | A type (predicate) is a behaviour whose evidence is yes/no | Lean | `beh_iff_of_subsingleton_co` |
| Definition, note 14 | The steps generate an orthogonal factorization system on families | CITED | Freyd–Kelly (small category, set of steps). Lean has the classes, not the factorization |
| Two fibres from the inside | Two routes in the bracketing calculus | Lean | `Pentagon.top`, `Pentagon.bot`, `top_ne_bot_localized` |
| Two fibres from the inside | `K a (I b)` reaches `a` by two runs counted as one | Lean | `SKI.kaib_one_run` |
| Reading code | Sameness under probes falls back to sameness after running | HAND, **qualified** | True for terms with a value. Two non-convertible terms with no value need not be separated (genericity). **Text fixed** (§2, E4) |
| Cards | Group words: cost of a run is an area | Lean | `cost_eq_area` (relator deletions, conjugation free) |
| Cards | Grid figure: least number of swaps = area between paths | standard | Inversion count. Not the Lean statement, which is about groups |
| Cards | Associativity: evidence can come back changed | Lean | `exists_beh_top_ne_bot` (ℤ-valued behaviour separates the routes) |
| Cards | Cost, higher types, processes, proofs | CITED/HAND | Not in Lean |
| What is kept | Over a value, CL fibres have no holes | MEMORY + Lean | Lévy: any two runs to a normal form are permutation equivalent [MEMORY, Terese ch. 8]. Then the normal form is terminal in the fibre, and `localization_trivial_of_terminal` / `beh_equiv_type_of_terminal_co` give no holes, with behaviours = evidence about the value. **Text updated** (E6) |
| What is kept | Pentagon is the hole left by the self-overlap | Lean | `top_ne_bot_localized` |
| Evidence along runs | Counter on the `ω ω` loop is a behaviour; lap = +1 | Lean | `SKI.omegaLoop'_wt` (the essay's order), `SKI.omegaLoop_permEq` |
| Evidence along runs | Inside `K a (ω ω)` the counter fails; a lap counts for nothing | Lean | `SKI.absorbed` |
| Evidence along runs | Extending the counter beyond the three terms | Lean on K-free terms, HAND with K | `SKI.wt_permEq`: S-steps along the rightmost branch, on K-free terms. A plain count of S-steps fails because S copies its last argument. **Text updated** (E7) |
| Three loops | `ω ω` is not filled | Lean (partial) | `SKI.not_absorbed'`: no run out of `ω ω` undoes a lap. That the loop is nontrivial in the fibre's groupoid is HAND |
| Footer | "nothing here has been checked by machine" | — | **Out of date. Text updated** (E8) |

## 2. Edits made to the essay text (`post/atoms-and-probes.html`)

Each edit is a factual correction or a status update. Prose voice kept; nothing else
touched. Diff against `9d8b555`.

- **E1** (§ Running): the `ω ω` terms "run only to one another" → run to one another in a
  cycle. Its own note already says further steps lead out of the figure.
- **E2** (§ Three equalities): "Each is a normal form, so no step leads from one to another"
  is not a reason, because fibres also contain backward steps. → by confluence, two different
  normal forms never share a fibre.
- **E3** (§ Types): "It is stronger than those … does their work" → simpler to state, not
  the same as any of them, and it does the part of their work that the fundamental lemma
  needs. Closure in both directions does not give Girard's CR3, which puts neutral normal
  terms in every candidate. Lean shows the fundamental lemma uses only the backward
  direction.
- **E4** (§ Reading code; card): "falls back to sameness after running" → for terms that
  have a value.
- **E5** (§ Cards): status sentence. Groups and associativity now partly machine-checked.
- **E6** (§ What is kept): the no-holes-over-a-value claim, split into Lévy (cited) and the
  step from a terminal value to no holes (Lean).
- **E7** (§ Evidence): extending the counter. The K-free part is done in Lean, and the
  rightmost-branch count is the reason why.
- **E8** (footer): what has and has not been checked by machine.

## 3. Lean added from the essay (`95590cb`)

`FormalComputation/SKI/Types.lean` and `FormalComputation/Predicates.lean`, listed above.
All are elementary. Their value is that the essay's own definition of a type is connected
to Theorem A by a proved statement.

## 4. Not done; options

- **The probe layer.** The essay's third ingredient, observation, is not in the formal
  definition. In Lean a presentation is `(P, S)`, the kind of answer is fixed to sets, and
  probes are not modelled. Formalizing it for CL would need:
  - Church–Rosser for CL (not in Mathlib);
  - contextual equivalence with the essay's "reads only its own variables" observation;
  - `I ≅ S K K ≅ S K S`;
  - "running ⇒ probes".

  This is a few hundred lines and several CI rounds.
- **Lévy.** Showing that `PermEq` is Lévy's equivalence, and that runs to a normal form are
  equivalent, needs residual theory. Stretch K9; heavy.

## 5. Where the essay and the technical notes now disagree

- **Ingredients.** The essay: a presentation is descriptions + steps + observation. The
  notes, `SUMMARY.md` and Lean: `(P, S)`, with observation spread over the knobs (`V`, probe
  shapes) in `notes/02`. The essay's line 149 ("steps settle which predicates are types;
  probes are the usual way of defining one") is consistent with Lean, where behaviours
  depend on the steps alone.
- **Variance.** The essay reads families covariantly (evidence carried forward). Lean's main
  presentation is presheaves. Both are proved, and they agree when the steps generate the
  runs, which they do in the essay's category of runs. No change needed.
- **Direction.** The essay does not use the "(P, E), not C" slogan, so the concern from the
  2026-11-18 assessment does not touch it.
