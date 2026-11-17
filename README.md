# formal-computation (working title)

A starting packet for a new repo: a relational, category-theoretic account of
computation, with a blog post and a Lean 4 formalization to be built from it.

Everything here came out of one long conversation (11–13 November 2026).
**Nothing in this packet has been machine-checked.** Hand arguments, cited
results and speculation are all present, and each is labelled.

## Layout

| Path | What it is |
|---|---|
| `SUMMARY.md` | The main ideas, up front. This is the front matter of the post. |
| `notes/01-…11-….md` | Detail sections: everything worked through, with status labels. |
| `PROOF_MAP.md` | Every definition, lemma, theorem and conjecture, with a pseudo-Lean signature, dependencies, tier and status. |
| `post/outline.md` | Proposed structure of the blog post and how it maps to the notes. |
| `CLAUDE.md` | Instructions for the Claude Code session that will build the Lean project and finish the writing. |

## Status labels

Used throughout the notes and the proof map.

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
