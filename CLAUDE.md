# Instructions for the Claude Code session

This repo starts as a packet of notes plus a proof map. Your job is to turn it
into (a) a Lean 4 + Mathlib project that verifies the proof map's tiers 1–3 and
(b) a finished blog post whose every "verified" claim links to a Lean
declaration.

## Ground rules

1. **The signatures in `PROOF_MAP.md` are pseudo-Lean and have never been
   compiled.** Treat them as intent. Your first job is to make them compile
   against current Mathlib. Mathlib names in the map were recalled or found by
   web search and may have moved; check each one (the list is in the map under
   "Mathlib anchors to verify").
2. **Never weaken a statement silently.** If a statement is false, needs an
   extra hypothesis, or has to be restated, record it in `PROOF_CHANGELOG.md`
   (create it) with the node ID, the old statement, the new one and why. Then
   update the affected note and `SUMMARY.md`.
3. **If something cannot be proved, demote it.** Change its status to [CONJ]
   in the map and the notes. Do not leave it marked as verified.
4. **No `sorry` and no new axioms** in anything the post calls verified. Run
   `#print axioms` on each headline theorem and record the output.
5. **Work in tier order**: tier 1, then 2, then 3. Do not start a tier until
   the previous one builds.
6. **Do not formalize the "not attempted" nodes.** They are cited or
   conjectural on purpose. The post states them as such.
7. **Prefer concrete and decidable** formulations for the examples (finite
   quivers, `decide`, explicit paths) over general theory.
8. **Variance matters.** Type families over terms are covariant (`A ⥤ Type`).
   Descriptions are representable presheaves (`Aᵒᵖ ⥤ Type`). State Theorem A
   for `A ⥤ Type`; state the normal-form and ind-object results for
   presheaves. See `notes/03-definition.md` §3.4 and `notes/08-coercion.md`
   §8.6.
9. **Keep the hand-argument honest.** Several results in the notes were argued
   quickly. If formalizing shows the argument was wrong, say so plainly in the
   changelog and in `notes/11-corrections-and-open-problems.md`.

## Suggested Lean layout

```
FormalComputation/
  Orth.lean            -- O1–O9   unique lifting, closure lemmas, coercion
  Presentation.lean    -- D1–D6   presentations, E, M, behaviours, conversions
  LocalSystems.lean    -- A1–A4   Theorem A
  Translation.lean     -- B1–B6   Theorem B
  Collapse.lean        -- C1–C4   the collapse lemma and its counterexample
  Pentagon.lean        -- P1–P3   associativity
  Dehn.lean            -- G1–G3   cost equals area
  SKI/
    Syntax.lean        -- K1–K3
    Weight.lean        -- K4, K7
    PermEq.lean        -- K5, K6, K8
```

## Order of work

1. `lake new`, add Mathlib, confirm a trivial file builds.
2. Create every module with all statements present and `sorry` bodies. Get the
   whole skeleton to compile. Log every statement that had to change.
3. Tier 1: `Orth`, `Presentation`, `LocalSystems`, `Translation`, `Collapse`.
4. Tier 2: `Pentagon`, `Dehn`.
5. Tier 3: `SKI`.
6. Write the post from `post/outline.md`, `SUMMARY.md` and the notes. Up front:
   main ideas and summary. After that: detail sections. Each theorem carries
   its status and, if verified, a link to the declaration.

## Definition of done

- `lake build` succeeds with no `sorry` in tiers 1–3.
- `PROOF_MAP.md` statuses match reality (verified / cited / conjecture).
- `PROOF_CHANGELOG.md` lists every statement change.
- The post exists, leads with the summary, and makes no claim stronger than
  its status.

## Things the human cares about

- A relational, structure-first presentation. Do not rewrite the ideas into
  set-theoretic language where a universal property is available.
- Size and finiteness conditions should be explained by what they buy
  (existence of a reflector, convergence of an iteration), never asserted.
- Higher coherence is to be introduced in a controlled way and flagged as such.
  The first post stays at the Set and Cat levels.
