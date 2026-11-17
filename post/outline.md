# Post outline

Working title: **Show me the holes: computation as a factorization system**

Structure requested: main ideas and summary up front, then detail sections
with the full working.

## Part I. Up front (short)

1. **The question.** What is computation, seen relationally, without bottoming
   out in sets? (`notes/01` §1.1)
2. **The answer in one paragraph.** The thesis from `SUMMARY.md`.
3. **The definition in ten lines.** (`notes/03` §3.2)
4. **The dictionary.** The table from `SUMMARY.md`.
5. **What is proved, what is cited, what is conjecture.** One list with
   statuses and links to Lean.

## Part II. Detail sections

6. **The motif.** Fibres of descriptions; the gauge analogy and where it
   breaks. (`notes/01`)
7. **The definition and why it has this shape.** Including the failed first
   attempt and the collapse lemma. (`notes/03`, `notes/06` §6.1)
8. **Theorem A: behaviours are local systems.** (`notes/03` §3.3, PROOF_MAP A1–A4)
9. **Example: associativity and the pentagon.** (`notes/04` §4.2)
10. **Example: SKI, the cocycle, and two kinds of divergence.** (`notes/04` §4.1, `notes/06`)
11. **Example: groups and the Dehn function.** (`notes/04` §4.3)
12. **Theorem B: morphisms.** Translations, simulations, completion. (`notes/05`)
13. **Coercion.** (`notes/08`)
14. **The knobs.** A map of the wider space, kept brief. (`notes/02`)
15. **Open problems and what comes next.** (`notes/11`)

## Deferred to a second post

- Type theories as adjunction-rule presentations; polarity. (`notes/07`)
- Dependent types: two fibres; the proof-relevant design. (`notes/07`)
- The arena and higher coherence. (`notes/09`)
- Tree calculus and the tight/loose reading of Church–Turing. (`notes/04` §4.6, `notes/05` §5.7)

## Style notes

- Lead with the claim, then the reason.
- Every theorem carries a status tag. Verified ones link to a Lean declaration.
- Explain every size or finiteness hypothesis by what it buys.
- Diagrams for every lifting argument (see `notes/08`).
