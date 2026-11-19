# 14. Tree calculus and interaction nets in the framework (working, 2026-11-19)

Source: the `tree-semantics` repository (Forgejo `maxine/tree-semantics`, main at
`5147cfa`), surveyed read-only. Lean names below are **checked** in that repository's
terms (CI run 1841; its index refuses `sorryAx`) unless marked otherwise. Paths are
relative to `TreeCalculus/`.

**Constraint.** `docs/interaction-nets/disp-ic.md` (disp's own net table) is marked
[disp] and is not to be published without Zya's agreement. Do not quote it in the
essays.

## 14.1 The calculi

**Tree calculus**, the triage presentation (`Tree.Eval`, Algebra.lean:506):

    △ △ y z → y                 (K)
    △ (△ x) y z → x z (y z)     (S)
    △ (△ w x) y △ → w           (triage: leaf)
    △ (△ w x) y (△ u) → x u     (triage: stem)
    △ (△ w x) y (△ u v) → y u v (triage: fork)

**Interaction nets**
- Lafont's interaction combinators γ, δ, ε with six rules (`combTable`,
  IxTable.lean:259), on a general substrate of port graphs.
- The interaction calculus of Fernández–Mackie / Salikhmetov (IxRevSal*). Lafont's
  combinators are not reversible (`comb_not_salConnected`).
- Taelin's Interaction Calculus / HVM is literature only.
- Tree calculus compiles to nets: `eagerTable`, 15 rules (IxTree.lean:128), sound and
  adequate (`eager_sound`, `adequate`, `finishes_iff_eval`).

## 14.2 Running

**Tree calculus**
- Confluent: `Tm.par_diamond` (Algebra.lean:771), `red_confluent` (:809),
  `church_rosser` (:850).
- Closed normal forms are the trees (`Tm.normal_closed`).
- There is no one-step diamond and no equal-length theorem, since S duplicates.

**Interaction nets**
- One-step diamond: `Ix.strong_confluence` (IxConfluence.lean:278).
- Disjoint firings commute to equal nets: `fire_commute` (IxCommutation.lean:96).
- Unique normal form and equal finishing length: `Steps.unique`, `Steps.equal_lengths`.
- Weak normalization implies strong: `no_infinite_run`.
- Every finishing run fires the same events, up to permutation: `Run.perm`,
  `event_invariance`.
- Runs are exactly the linear extensions of causality: `linearExtension_realization`.

## 14.3 Probes that read code are inside tree calculus

- **The I / S K K pair.** `idT = △(△(△△))△` is S K △, and `idT' = △(△(△△))(△△)` is S K K.
  Both are the identity, and a probe reads `tt` from one and `ff` from the other
  (`Tree.intensional_observation`, Meaning.lean:794). The probe reads the code's right
  child.
- No nontrivial model is extensional: `TreeAlgebra.not_extensional`.
- A tree decides equality of trees (`Tree.exists_eq`). Rice: a total, behaviour-respecting
  test is constant (`Tree.rice`).
- **K1 criterion.** A nontrivial PCA is K1-equivalent iff it has internal quote and
  unquote (`pk1_equiv_iff`).
  - SKI modulo conversion is not K1-equivalent (`pk1Conv_not_equiv`).
  - Trees are (`pk1Tree_equiv`).
  - The net PCA equals the tree PCA (`pk1Net_eq_tree`).
- **In contextual form.** A β-equal pair is distinguished once contexts may quote
  (`irs14CbnBeta_quoted_distinct`).

## 14.4 Types

- Types are PERs on trees (`Tree.PER`, `PER.arrow`), with a fundamental lemma
  (`Tree.abstraction`) and a typed calculus (`HasType.sound`, `terminates`).
- Code equality is typable only at boxed types `□A` (`eq_typed`, `eq_not_extensional`).
- An effective tripos and an elementary topos. "Is the effective topos" is only
  partly checked.

## 14.5 Cost

- **Tree calculus.** Cost is fixed by the evaluator (`EvalC.det`) and depends on the
  strategy. Eager evaluation is incomplete (`eager_incomplete`).
- **Nets.** The interaction count is the same for every finishing run (`exact_cost`,
  `every_finishing_run`), with an exact recursion: K costs 2+|z|, and copying or erasing
  costs `size`.

## 14.6 Analogues of the essay's examples

| SKI (essay 1) | Tree calculus | Nets |
|---|---|---|
| I, S K K: same under probes, different fibres | `idT`, `idT'`: same under running-in-context of values, **different under probes**, which can triage | the same as trees (`pk1Net_eq_tree`) |
| ω ω | `omegaT = fork (stem idT) idT` (S I I) | diverges iff no value (`divergent_infinite`) |
| K a (ω ω): two runs, one value | `K leaf (omegaT omegaT)`: no value under strict `Eval` | 27 interactions on the lazy net (`discarded_divergence`) |
| runs counted as one (Lévy squares) | parallel diamond only | `fire_commute` is the square, and runs are linear extensions of one causal order |
| cost: not a behaviour in general | evaluator cost, strategy-dependent | cost **is** a function of the endpoints |

## 14.7 What this gives the framework [inferred]

**1. Abstraction is a property of the calculus, not of the observer.**
- In SKI, probes read only what they supplied, so probes are coarser than running.
- In tree calculus, a probe can triage its argument. "Probes that read code" is then
  the calculus's own observation, and on terms with a value, sameness under probes
  collapses to sameness after running.
- This is our general `codeEq_iff_conv`, realized internally. The K1 criterion says
  which: a calculus is K1-equivalent iff it can quote.

**2. Lens-built types reach code in tree calculus.**
- Over SKI, lens-built types cannot express "runs to I". In tree calculus the probes can
  read code, so the corresponding types can.
- The price is extensionality. Code equality is typable only at `□A`, which is the
  modal boundary.

**3. In nets, cost becomes invariant.**
- With a one-step diamond and equal lengths, the step count is the same along every run
  between two nets. So it is a behaviour, valued in ℕ, a cost that sees no direction.
- Interaction nets are the calculus where the essay's cost card stops dropping
  invariance.
- The run category modulo squares is a trace monoid: runs are linear extensions of one
  causal order. Lévy's permutation equivalence becomes Mazurkiewicz trace equivalence.

**4. Holes.**
- SKI's ω ω carries a ℤ-valued lap counter. Under the one-step diamond, every finite loop
  in a net would be filled by squares; whether that holds needs checking.
- Tree calculus inherits SKI's situation through its S rule.

## 14.8 Plan

**Lean, in this repository**
1. Tree calculus as an instance of `Calculus` (`FormalComputation/Tree/`):
   - port the syntax and parallel-reduction confluence;
   - the probe separating `idT` from `idT'`, as a reading of variables:
     `probe [ ] x y` reads `x` for one and `y` for the other;
   - hence "not the same under probes", against "the same after running in every
     argument".
2. The interaction-net facts are cited from tree-semantics (pinned commit), not
   re-proved. An abstract instance is possible: a calculus with a one-step diamond and
   equal lengths has step count as a behaviour.

**Essay 1 additions**
- A short section, or a card, "A calculus whose probes read code": tree calculus, with
  the idT/idT' figure.
- One paragraph on nets: same values, and every run the same length, so cost is
  invariant.
