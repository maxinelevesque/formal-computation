# "Atoms and Probes" for maxine.science: handoff report

From the formal-computation thread (machine: the dev machine), 2026-11-20. For the maxine.science
thread, with Maxine relaying. This is everything the site side needs to fit the essay into
the writing repo's new data model for interactives, and the questions we need answered.

## 1. What the piece is

- **Title:** *Atoms and Probes*.
- **Dek:** "Computation is what a type forgets."
- **Series:** essay 1 of three. Essay 2 and a technical companion follow, and are not
  part of this handoff.
- **Content:** a long-form essay with sidenotes (Tufte layout) and about a dozen
  interactive SVG figures. It explains a framework in which a calculus is a
  presentation: descriptions, steps, and an observation (probes). The worked example is
  combinatory logic (SKI).
- **The calculus switch.** A three-way control (Combinatory logic · Tree calculus ·
  Interaction nets) redraws nine figures in the chosen calculus. A short note under each
  figure says what changes. The choice is kept in the URL hash: `#calc=tree`,
  `#calc=net`; SKI is the default.
- **Status:** in editorial review round R1. Five independent passes are done:
  narrative, Lean references, literature references, figures and style. Their
  findings are being applied now. It is **not ready to publish**. Please plan the
  integration, but don't publish anything until Maxine signs off on R1.
- **Mechanized claims:** the claims carry small superscript "lean" links to their Lean
  proofs.
  - These point to the public GitHub mirror,
    `github.com/maxinelevesque/formal-computation`, pinned to a commit.
  - Some links point to `github.com/maxinelevesque/tree-semantics`, which is private
    until Maxine makes it public. Those 404 until then; that is expected.

## 2. The artifact, as it stands

**Source of truth.** The repository is `formal-computation`: Forgejo
`maxine/formal-computation` (private, runs CI), mirrored publicly at
`github.com/maxinelevesque/formal-computation`. The file is `post/atoms-and-probes.html`.

**Shape.** One self-contained HTML document, about 370 KB.
- It has inline `<style>` and two inline `<script>` blocks.
- There are no images and no build step; every figure is SVG drawn by the script.
- The first script block is generated: `scripts/inline-calc.py` copies
  `post/lab/{ski,tree,net,graph}.js` between `/* BEGIN CALC … */` and `/* END CALC */`.
  The site should treat the file as built output.
- The calculus code has its own tests: `node post/lab/test.js` and
  `node post/lab/essay-test.js`.

**External requests**
- Google Fonts: IBM Plex Mono, IBM Plex Sans, Source Serif 4. The site may want to
  self-host these or map them to its own fonts.
- Outbound links only, otherwise:
  - github.com, for the Lean links;
  - doi.org, for citations;
  - one link to the tree-calculus specification site.

**Layout assumptions**
- Main column about 594 px, with a sidenote margin to the right on wide screens.
- Breakpoints at 640 px (narrow figures) and 820 px (the tree-calculus bundle switches
  to a tall layout). The figures redraw when the window crosses these.
- `prefers-color-scheme: dark` is supported.
- Reduced motion is being added in R1.

**Global state the page uses**
- The whole document and `<body>`.
- `location.hash`: `#calc=…`, plus section anchors such as `#mechanized`.
- `html[data-calc]`.
- Element ids throughout.

The figure script assumes it owns the page. Embedding it inside another page's DOM
would need isolation (an iframe or shadow DOM) or a refactor; see §4.

**Sidenotes** use the Tufte CSS checkbox pattern (`label.sn-toggle` + `input.sn` +
`span.sidenote`).

## 3. The writing repo as we found it (read-only, public GitHub)

- `maxinelevesque/writing` at `main` 55daa3d:
  - pieces live in `pieces/<slug>/index.md`, as Markdown with semantic frontmatter
    (`SCHEMA.md`);
  - `scripts/validate` is the publish gate;
  - CI publishes `site.standard.document` atproto records (`records.json`) and
    dispatches a rebuild of `maxinelevesque/maxinelevesque.github.io`.
- **Neither repo has an interactives data model on `main` yet.** We assume it is on a
  branch, or on the other machine.

## 4. Questions for the maxine.science thread

1. **The model for an interactive piece.** Which of these does it use?
   - (a) A full HTML document served as is, in an iframe or as its own page.
   - (b) An HTML fragment plus script and style assets, mounted into the site layout.
   - (c) Markdown prose with embedded figure components.

   (a) fits this essay today with no changes. (b) needs us to scope the CSS and make
   the script mount into a container. (c) is a rewrite and not planned.
2. **Where the built file lives in `writing`.** For example `pieces/atoms-and-probes/`,
   with `index.md` frontmatter plus an `interactive.html` or an `assets/` folder. Is
   there a size limit?
3. **Frontmatter for an interactive piece.** Is there a field for the HTML entry point,
   and one for a "requires JavaScript" fallback?
4. **atproto.** What does the `site.standard.document` record carry for an interactive
   piece, and what is its plain-text or Markdown fallback?

   We can supply a static Markdown version of the prose, with figure stills and
   captions, if the model wants one.
5. **Fonts and theme.** Should the essay keep its own typography, or take the site's? Is
   its dark mode wanted, or does the site impose its theme?
6. **The URL and the hash.** The canonical URL would be
   `https://maxine.science/writing/atoms-and-probes`. Is that right? The essay needs
   `#calc=…` and in-page anchors to survive.
7. **The update flow.** We propose that formal-computation stays the source, and that a
   script there writes the built essay into a `writing` checkout as a PR or commit on a
   branch. Maxine publishes by merging. Does the site side want a different handoff,
   such as a release artifact or a pinned commit?
8. **Previews.** We already host private snapshots on the tailnet (§5). Does the site
   have its own preview of `drafts/`, and should the essay go there instead?

## 5. Private preview on the tailnet (the dev machine)

- **URL:** https://the dev machine.taila07ffd.ts.net:8443/. It is tailnet only, with no Funnel.
- **How it is served:**
  - The user systemd unit `fc-preview.service` runs a static file server on
    127.0.0.1:8770, serving `~/srv/fc-preview`.
  - One `tailscale serve` rule exposes it on https port 8443.
- **Snapshots:** `formal-computation/scripts/preview.py LABEL [NOTE]` copies the essay to
  `~/srv/fc-preview/LABEL/` and updates the index page.
  - `r1-frozen` is the copy the reviewers read.
  - `r1-applied` follows when the review edits are in.
- **Switching calculus:** add `#calc=tree` or `#calc=net` to any preview URL.

## 6. Provenance and privacy

- Commits in formal-computation are authored as `m@maxine.science`.
- The public mirror is a filtered history with private infrastructure removed.
- No personal email or private host names appear in the essay.
- Nothing from Conatus or studio work is involved.

## 7. What happens next on this side

1. Finish applying R1, run the diff check, re-pin the Lean links, and post
   `r1-applied` to the preview for Maxine.
2. Maxine signs off, or starts round R2.
3. Once the maxine.science thread answers §4, write the export script (a writing-repo
   branch or PR) and adapt the essay if the model needs a fragment rather than a
   document.
