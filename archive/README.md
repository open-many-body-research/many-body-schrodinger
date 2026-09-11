# Archive

`v1.0-research-notes/` holds the written research record behind the v1.0 foundation: 339 Markdown notes on proofs, audits, reading records and computation reports, produced during AI-assisted exploratory work before publication.

**These notes are not authoritative.**
- Their "PROVEN", "independently reviewed", "sealed" and similar labels are the original authors' own wording.
- In particular, every "review" in these notes was written by an AI agent working inside the same pipeline.
- The only authoritative statement of what is established is [`claims/registry.yaml`](../claims/registry.yaml), summarized in [`STATUS.md`](../STATUS.md).

**Why they are included.** The notes contain the complete paper arguments behind the P1 claims (S2, S5, S8), the H₂ and helium method notes, and literature reading records. Contributors reviewing or extending those claims need them.

**What was changed.**
- Local file paths, host names and user names were removed, so paths refer to the private workspace layout and many internal links are broken.
- A banner was added at the top of each file.
- Nothing else was changed.

**What was left out.**
- Full-text copies of published papers (cite them instead; see `docs/bibliography.md`).
- Agent session logs, prompts and resume files.
- Build caches and bulk data.
- The Hubbard-model exploration (see sector S9).

| Directory | Contents |
|---|---|
| `reports/` | The main reports of each research stage. `RWA_REPORT.md` contains the **withdrawn** "Theorem T PROVEN" claim, and `H2_CERTIFICATION.md` is unfinished. |
| `research/`, `helium_research/` | Literature reading records with citations, plus method notes |
| `nogo/` | Physical energy scales and the status of hardness results |
| `rwa_proof/`, `dyadic_proof/` | Paper arguments for S8-001 and S8-002 |
| `h2/` | H₂ separator (S3-003), moment theory, quadrature notes |
| `rate_decision/` | Comparison of helium dictionaries (source of S3-002) |
| `audit-v1/` | The first post-freeze audit: analytic, approximation, arbitrary-N, computation, errata, lithium |
| `continuation/` | Later paper checkpoints, audits and reviews, box-solver notes |
