> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual coordinate weak jets and compact-test identities

A full mixed triangular state of total order m now yields an actual coordinate weak-jet family D(w) for every interleaved word in the four Y directions and the spectator directions. The definition ProductCoordinateWeakHk requires D([])=f, membership in L2 on the region with a common squared-norm budget W for each word of length at most m, and the genuine local weak derivative identity from D(w) to D(i::w) for every next coordinate. This is a weak derivative representation, not a family defined only by norm bounds.

The construction projects each interleaved word to its Y and T subwords. Their lengths sum to the original length. Actual mixed derivative chains, already proved by weak commutation, give the next coordinate identity; no new regularity or norm factor is introduced.

For compact real smooth tests supported in the region, the exact identity is

    integral φ D(w) = (−1)^length(w) integral TestWord(w,φ) f.

TestWord recursively transposes the derivative order: TestWord(i::w,φ)=TestWord(w,D_iφ). Its smoothness, compact support, and support inclusion are proved, as is integrability of both sides from the region L2 membership. The identity itself can be instantiated from any genuine finite coordinate chain; the separate membership theorem prevents treating a totalized nonintegrable integral as a weak derivative certificate.

Both modules compile and strict v5 audit 20260910T213019_416716Z covers twelve declarations, with only the standard foundational axioms (two list projections use none). Exact expanded statements and source definitions were inspected. Existing pinned caches were reused; no new isolated source rebuild was run, and these files are outside the earlier 671-target rebuild snapshot. Prior PASS bytes and all failed logs are preserved.

The bridge does not by itself prove the analytic initialization or identify a pre-existing library H^m norm. Its next consumer selects canonical coordinate words for actual multiindices and sums their derivative L2 norms. An H12 count alone is not this derivative bridge. No factorial, approximation or full Theorem T claim is made here.

Frozen provenance: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; report THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
