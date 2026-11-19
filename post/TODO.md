# Post to-do: "Atoms and Probes"

- [ ] **Review DAG for editorial steps: specification.** Maxine will give the flow. Encode it
      here (or in `post/REVIEW.md`): the nodes (each editorial pass), their inputs and
      outputs, the order between them, and what each pass may change.
- [ ] Orthogonal model review over the essay, run through the review DAG.
- [ ] Observation as an ingredient: decide on `notes/12-observation.md` (questions in
      §12.6), then update the essay's definition section, the three equalities, and the
      cards, and formalize (§12.5).
- [ ] Check the Lévy fact used in "What is kept" (any two runs to a normal form are
      permutation equivalent) against Terese, *Term Rewriting Systems*, ch. 8.
- [ ] Lean links in the essay: inline marks and a "What has been checked by machine"
      section, pinned to a commit on the public mirror (`scripts/lean-links.py`).
- [ ] Publication on maxine.science: coordinate with the site threads on how posts with
      interactives are published now.
- [ ] Decide what `post/post.md` becomes (technical companion, or retired).
- [ ] Public mirror hygiene: `.forgejo/workflows/ci.yml` names internal hosts; keep or
      scrub. Push to both remotes (`origin` Forgejo, `github`) on every change.
