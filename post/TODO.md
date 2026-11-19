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
- [x] `post/post.md` is now `post/technical-companion.md`; the series plan is `post/SERIES.md`.
- [ ] Technical companion: add the observation layer, the three-classes theorem and the probe layer (`post/SERIES.md`).
- [x] Research: Turi–Plotkin and the bialgebraic line (`notes/13`: lineage, logical
      connections, HO-MOS, open maps, AWFS; synthesis in §13.0).
- [ ] Essay 2: write around §13.0 (invariant vs directed observers; distributive laws;
      runs with 2-cells), with SKI, tree calculus and interaction nets.
- [x] Essay 1: tree calculus (S K △ / S K K separated by a triage probe, mechanized) and
      interaction nets (Lévy sidenote, cost card). `notes/14`.
- [ ] Essay 1: the classification sentence and the card sort (`post/SERIES.md`).
- [x] `tree-semantics` will be made public (Maxine, 2026-11-19). Link it pinned to `5147cfa`;
      the links are broken until then.
- [ ] **The calculus switch** (`notes/15`): every SKI interactive in essay 1 also in tree
      calculus and interaction nets, behind one toggle.
- [ ] Lean next: the three-classes theorem for families (Yoneda); V-valued pairings
      (directed observers); a calculus with a one-step diamond has step count as a
      behaviour (interaction nets, abstractly); SKI runs as a DynPresentation.
- [x] Public mirror hygiene: the mirror is a filtered copy of main
      (`scripts/mirror/publish.sh`): the CI workflow, `scripts/fj-ci.py` and
      `scripts/mirror/` are dropped and private host names replaced, in every commit.
      History rewritten 2026-11-19. On every change: push `origin`, then run the
      publish script (never `git push github`).
