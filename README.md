# formal-computation (working title)

A starting packet for a new repo: a relational, category-theoretic account of
computation, with a blog post and a Lean 4 formalization to be built from it.

Everything here came out of one long conversation (11–13 November 2026).
The packet arrived with nothing mechanized. Since 2026-11-17 tiers 1–3 of
`PROOF_MAP.md` are proved in Lean (`FormalComputation/`, status [LEAN]); every
other claim keeps its label.

## Public mirror

This repository is published at
[github.com/maxinelevesque/formal-computation](https://github.com/maxinelevesque/formal-computation).
The Lean build runs on a private CI runner. The mirror omits the runner's workflow
file and helper script; everything else, including every Lean file, is the same.
`AXIOMS.md` records the axiom audit from each build. Commit hashes cited in the
notes, and in the essay's Lean links, are mirror commits.

## Layout

| Path | What it is |
|---|---|
| `SUMMARY.md` | The main ideas, up front. This is the front matter of the post. |
| `notes/01-…11-….md` | Detail sections: everything worked through, with status labels. |
| `PROOF_MAP.md` | Every definition, lemma, theorem and conjecture, with a pseudo-Lean signature, dependencies, tier and status. |
| `post/SERIES.md` | The three pieces (essay 1 "Atoms and Probes", essay 2, technical companion) and what goes in each. |
| `post/atoms-and-probes.html` | Essay 1. |
| `post/technical-companion.md` | The technical companion (formerly `post/post.md`). |
| `CLAUDE.md` | Instructions for the Claude Code session that will build the Lean project and finish the writing. |

## Status labels

Used throughout the notes and the proof map.

- **[LEAN]** proved in Lean 4 + Mathlib in this repo, with no `sorry` and only the standard axioms (`AXIOMS.md`). The proof map gives the declaration.
- **[HAND]** argued by hand in the conversation. Believed, not checked.
- **[CITED]** a published result. The reference was found by search and is linked in `notes/10-prior-art.md`.
- **[MEMORY]** a published result recalled from memory, not re-verified. Check before relying on it.
- **[CONJ]** a precise statement we expect to be true and have not proved.
- **[SPEC]** speculation or analogy. Not yet a precise statement.
- **[OPEN]** a known gap.

## How to use this packet

1. Create a new repo from this directory.
2. Read `SUMMARY.md`, then `PROOF_MAP.md`.
3. Hand the repo to a Claude Code session. `CLAUDE.md` tells it what to do first.
4. The Lean work goes tier by tier (see `PROOF_MAP.md`). Anything that fails is
   fixed in the notes or demoted to a conjecture, and the change is logged.
5. The post is written last, from the verified statements.

## Scope of the first post

Set and Cat levels only. No ∞-categories and no type-theory design. Those are
recorded in the notes (07, 08, 09) and are intended for a second post.
