# The series

Decided with Maxine on 2026-11-19. This file replaces `post/outline.md`, which
outlined the technical draft alone. The project is published as three pieces.
`notes/` holds the working, and each piece draws on it.

| Piece | File | Reader | Status |
|---|---|---|---|
| Essay 1: **Atoms and Probes** | `post/atoms-and-probes.html` | wide; no category theory assumed | drafted; review round R1 next (`post/REVIEW.md`) |
| Essay 2 (working title open) | not started; outline below | readers of essay 1 | outline |
| **Technical companion**: *Show me the holes: computation as a factorization system* | `post/technical-companion.md` (formerly `post/post.md`) | category theorists, logicians | draft of 2026-11-17; to be extended (below) |

The two essays are narrative. They state results at the strength they are
known and link to the companion and the Lean development for proofs. The
companion is the reference. It holds every definition and theorem with its
status tag, and it does not need the essays.

## Essay 1: Atoms and Probes

The six terms, three equalities (text, running, probes), types as predicates
that do not leak, the fundamental lemma, the cards, and what is kept and lost.
Observation appears as probes. The planned additions are small:
- one sentence saying that an observation is any pairing of descriptions with
  observers, and that the essay studies probes;
- the cards sorted by which of the four properties of `notes/12` §12.3 they
  drop.

## Essay 2: outline

Material planned for the second post since the packet (`notes/07`, `08`, `09`,
`04` §4.6, `05` §5.7):
- **Type theories as presentations** whose rules are units and counits of
  local adjunctions, and what polarity predicts about η-laws (`notes/07`).
- **Dependent type theory has two fibres**: definitional equality and identity
  types, and the pain points on the seam between them (`notes/07`).
- **Types built from lenses**: types as sets of tests, built by composing lenses,
  with arrow types as the first example. This continues essay 1's types and is
  mechanized for SKI (`notes/12` §12.7).
- **Observers that see direction** (candidate centre of the essay; research in
  `notes/13`). Invariant observers give algebra: what a term equals. Observers
  that see direction give coalgebra: what a term does. The two meet in Turi and
  Plotkin's bialgebraic semantics and the work around it. This goes in essay 2
  if the research bears out what we have re-found and where the framework
  generalizes.
- **The arena and higher coherence** (`notes/09`), briefly.
- **Tree calculus and a tight and loose reading of Church–Turing**
  (`notes/04` §4.6, `notes/05` §5.7).

## Technical companion: outline

The draft follows the original outline:
- Part I, up front: the question, the answer, the definition, the dictionary,
  and the status list.
- Part II, the detail:
  - the motif;
  - the definition;
  - Theorem A;
  - the pentagon;
  - SKI;
  - groups and Dehn;
  - Theorem B;
  - coercion;
  - the knobs;
  - open problems.

Additions planned since:
1. **Observation as a pairing** (`notes/12`, decided 2026-11-19), with families
   as the special case. Lenses. `T^⊥` as types. Mechanized:
   `Observation.lean`, `SKI/Lenses.lean`.
2. **The three equalities as three classes of observers**, and the Galois
   connection between observers and equalities (`notes/12` §12.2; to
   mechanize).
3. **The four properties** of the well-behaved case and what each buys
   (`notes/12` §12.3).
4. **The SKI probe layer**: confluence, contextual equivalence, the six terms,
   and reading code (`SKI/Confluence.lean`, `SKI/Probes.lean`).
5. **Directed observers**, formally: `V`-valued pairings and the
   lifting picture (`notes/12` §12.8, `notes/13`), at whatever strength the
   research supports.
6. **Lévy**: the normal derivation theorem and the counting of runs used by
   essay 1 (Huet–Lévy part I, Thm 3.26).

## Style notes (all three pieces)

- Lead with the claim, then the reason.
- Every theorem carries a status tag. Mechanized ones link to a Lean
  declaration.
- Explain every size or finiteness hypothesis by what it buys.
- Diagrams for every lifting argument (see `notes/08`).
- The essays pass the review DAG in `post/REVIEW.md` before publication.
