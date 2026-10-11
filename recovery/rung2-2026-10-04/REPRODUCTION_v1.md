# Initial requested closure: successful replay

The source snapshot in [MANIFEST.json](MANIFEST.json) passed a clean local-source rebuild and complete expanded-statement/axiom replay on commit `098acd707088173945b94f52e5320ae02ef64bad`.

- All 1,159 local modules compiled successfully from source into an initially empty output directory.
- All 1,721 public declarations in all 409 restored continuation modules passed the expanded-statement and axiom checks.
- The only reported axioms were `propext`, `Classical.choice` and `Quot.sound`; no printer omission/fallback or missing axiom report was accepted.
- Every source hash was checked before and after the run, and the tested checkout remained clean and unchanged.

The [full receipt](reproduced/summary.json) records the tested Git commit/tree, exact pinned versions, compiler hash, commands and source/object/log hashes. All compile logs and expanded-statement sources/outputs are retained in [the archive](reproduced/logs-and-expanded-statements.tar.gz), with a per-file [archive manifest](reproduced/ARCHIVE_MANIFEST.json). Extract it into a new directory to inspect the files named by the receipt. Historical project objects are not published.

The official Lean compiler/core and pinned third-party compiled libraries were reused. Every local foundation and continuation module in the requested closure was rebuilt; Lean and Mathlib themselves were not rebuilt from source. This is scoped machine verification, not a human definitions review or a claim of mathematical completion.

Later sealed developments have their separate [latest-stage recovery](../rung2-latest-2026-10-04/README.md). This receipt and the initial manifest remain unchanged.
