# Editorial review of "Atoms and Probes": the review DAG

Specified by Maxine on 2026-11-19. This file says which passes run, what each one
reads and writes, what it may change, and in what order. The review is
**orthogonal**: every review pass is run by a model other than the one that wrote
the text (through T3 `delegate_task`), on a frozen copy of the essay, without seeing
the other passes' findings.

## The graph

```
                ┌─> N  narrative ──┐
                ├─> L  Lean refs  ─┤
 F0 freeze ─────┼─> C  citations  ─┼─> T triage ─> A apply ─> D diff check ─> S0 sign-off
                ├─> G  figures    ─┤                 │              │
                └─> Y  style      ─┘                 └── a changed claim goes back to M
 M  semantics (SYNC.md) ── must be current before F0, and again in D
```

- **Reviews run in parallel.** N, L, C, G and Y read the same frozen copy and
  are independent of one another.
- **Edits run in sequence**, in the order N → G → L, C → Y. Structure changes
  first. References are fixed after the text they hang on has stopped moving.
  Style comes last, so that it polishes the final sentences.
- **A round** is F0 → S0. Run rounds until a round has no blocking findings, at
  most three. A later round's reviewer gets the original brief, the previous
  findings and the responses to them, and any objections still open.

## Nodes

Each review node writes `post/review/R<round>/<node>.md`. It holds a list of
findings, each with:
- a location (section and a short quote);
- the problem;
- a severity: **block**, **should** or **could**;
- a suggested fix.

Reviewers do not edit the essay.

### M. Semantics (prerequisite; owner: author)

Every mathematical claim matches what is proved, cited or argued.
- Input: the essay, `post/SYNC.md`, the Lean development, `notes/`.
- Output: `post/SYNC.md` brought up to date.
- *Block* if a claim is stronger than its support.

### F0. Freeze

Record the commit of the essay under review in `post/review/R<round>/README.md`.
Every review pass reads that commit.

### N. Narrative

1. **Builds linearly.** Each section uses only what came before it. No forward
   references are needed to follow an argument.
2. **Working memory.** Nothing defined far back is used without being restated
   nearby or carried by a memory device: a sidenote, a recap line, a figure
   label, a persistent legend. Flag every use of a term or example more than a
   section after its last mention that has no such device.
3. **Terminology.** Each technical word has one meaning throughout. No ordinary
   word is used in a technical sense without being introduced as such. Flag
   words used more broadly than their definition.
4. **Self-contained.** Every concept the argument needs is introduced in the
   essay. Nothing depends on conversations, the notes or outside context. A
   citation may support a claim, but it cannot replace an explanation the
   argument needs.
5. **Audience.** The essay is readable by people from several backgrounds:
   - programmers;
   - logicians and type theorists;
   - category theorists;
   - mathematicians without programming-languages background.

   Flag passages that only one of these groups can follow.

*Block:* an undefined concept that the argument needs, or a step that does not
follow from what came before.

### L. Lean references

1. Every claim the essay calls mechanized has a `lean` mark, and every mark's
   declaration states what its sentence says: not more, not less, not a
   neighbour.
2. The "Mechanized" table and its "Not mechanized" list together cover every
   formal claim in the essay.
3. All links resolve to the declaration line at the pinned mirror commit
   (`python3 -I scripts/lean-links.py SHA --check`).

*Block:* a mark whose declaration says something different from its sentence.

### C. Literature references

1. Every result that is not the essay's own has a citation in the note beside
   it.
2. Each citation gives a DOI link (`https://doi.org/…`) where one exists, and
   otherwise a stable URL or the full bibliographic record.
3. The reviewer resolves each DOI and checks that it is the cited work. Where
   possible, the reviewer also checks that the cited claim is in it, and gives
   the theorem, section or page.
4. "Recalled from memory" sources are flagged until confirmed.

*Block:* a citation that does not support its claim, or a DOI that resolves to
something else.

### G. Figures and interaction

1. **Purpose.** Each figure shows the idea of its section at a glance. What to do
   with it is obvious without instructions, and doing it shows the point.
2. **Style.** The figures follow the essay's influences:
   - Tufte: data ink, small multiples, sidenotes and figures in the flow of the
     text, no chart junk;
   - Butterick: measure, leading, type hierarchy, no faux bold or italic,
     restrained colour;
   - Bret Victor: direct manipulation, visible state, immediate feedback,
     examples the reader can change.
3. **Beauty.** Figures are consistent with one another in palette, stroke,
   labels and motion.
4. **Robustness.** Figures work at phone width, and in light and dark modes.
   They are keyboard operable, respect reduced motion, and have enough contrast.
   The reviewer views each figure in a browser and attaches screenshots.

*Block:* a figure that shows something false, or one whose interaction does not
work.

### Y. Style

1. **No AI tropes.** Flag each instance and give a plain rewrite:
   - "not X but Y" and "not just X, Y" frames;
   - lists of three by reflex;
   - colon reveals and one-line dramatic paragraphs;
   - rhetorical questions used as transitions;
   - closing sentences that restate the paragraph;
   - "it's worth noting", "crucially", "importantly", "in other words",
     "here's the thing", "at its core", "delve", "landscape", "tapestry",
     "rich";
   - stacked hedges;
   - em-dash chains;
   - signposting such as "Let's", "Now we", "This is where X comes in";
   - grandiose framing.
2. **The essay's register.** Plain words, active verbs, claims stated at the
   strength they are known. Status is said once, not repeated.

*Block:* none. Style findings are *should* or *could*.

### T. Triage (owner: author)

Merge the five finding lists. For each finding, record **accept**, **reject**
(with the reason) or **defer** in `post/review/R<round>/triage.md`.

### A. Apply (owner: author)

Make the accepted edits in the order N → G → L, C → Y.

Each pass is limited in what it may change:

| Pass | May change |
|---|---|
| N | order, explanation, recaps |
| G | figure code and CSS |
| L, C | links and notes |
| Y | wording only |

Any edit that changes what a sentence claims goes back to M.

### D. Diff check (owner: author)

Run M again, on the diff since F0 only. Then run `lean-links.py --check`.

### S0. Sign-off (Maxine)

Maxine reads the triage and the diff and either accepts or starts another round.

## After review

Publish on maxine.science (see `post/TODO.md`).
