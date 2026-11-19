# Post to-do: "Atoms and Probes"

- [x] **Review DAG for editorial steps: specification.** Maxine's five passes (narrative,
      Lean references, literature references with DOIs, figures, style), encoded in
      `post/REVIEW.md` with semantics as prerequisite and diff check.
- [ ] Orthogonal model review over the essay: round R1 of `post/REVIEW.md`.
- [ ] Observation as an ingredient: decide on `notes/12-observation.md` (questions in
      §12.6), then update the essay's definition section, the three equalities, and the
      cards, and formalize (§12.5).
- [x] Check the Lévy fact used in "What is kept" (any two runs to a normal form are
      permutation equivalent). Holds for finite runs in orthogonal TRSs: Huet–Lévy 1991
      part I, Thm 3.26 (normal derivation theorem), proof by projection; van Oostrom–de
      Vrijer, ENTCS 70(6) 2002, Thm 7.1 (the equivalences coincide). Terese §8.7's residual
      system has a published flaw (Kohl–Middeldorp, CADE 2019) that only affects overlapping
      rules. Essay sidenote now cites the theorem. Not mechanized.
- [x] Lean links in the essay: inline marks and a "Mechanized" section, pinned to a
      commit on the public mirror (`scripts/lean-links.py`).
- [ ] Publication on maxine.science: coordinate with the site threads on how posts with
      interactives are published now.
- [ ] Decide what `post/post.md` becomes (technical companion, or retired).
- [x] Public mirror hygiene: the mirror is a filtered copy of main
      (`scripts/mirror/publish.sh`): the CI workflow, `scripts/fj-ci.py` and
      `scripts/mirror/` are dropped and private host names replaced, in every commit.
      History rewritten 2026-11-19. On every change: push `origin`, then run the
      publish script (never `git push github`).
