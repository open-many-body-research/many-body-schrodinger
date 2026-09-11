> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit weak Grushin one-step gain for raw local data

**Formal theorem, with explicit hypotheses; PASS.** The final source and expanded statement compile in the pinned environment, using only `propext`, `Classical.choice`, and `Quot.sound`. No derivative of the raw input is assumed.

The actual space is R⁴ × R^κ for arbitrary finite κ with product Lebesgue measure. The operator is the existing `splitGrushin c oscillatorBasis 0`, with c>0. Fix an open domain Ω, smooth compact cutoffs χ,η, and an open W containing support χ on which η=1. Assume support η⊆Ω. Supply the same actual cutoff-function bounds M,A,B,D,Q as `local_weak_grushin_explicit_one_step`, with B,D,Q≥0.

There are compact K and open V, chosen before the raw input/source functions, such that support η⊆V⊆K⊆Ω and support χ⊆K. For raw locally-L² data G,h satisfying the compact-test equation P_c G=h on Ω, define

\[
F=\int_K |G|^2,\qquad H=\int_K |h|^2,\qquad
J=(4A^2+16B(D/2+Q))F+(2M^2+8BD)H.
\]

There is an actual L² class U=χG with Y/T first weak jets and ordered YY second weak jets, satisfying

\[
\|U\|_2^2\le M^2F,\quad
\sum_i\|D_{y_i}U\|_2^2\le2M^2F+	frac34J,\quad
\sum_j\|D_{t_j}U\|_2^2\le J/(16c),\quad
\sum_{i,j}\|D_{y_j}D_{y_i}U\|_2^2\le	frac32J.
\]

The proof constructs global L² classes by restricting G,h to K, preserves the PDE on V through support locality of the test operator, then applies the audited explicit one-step theorem. Exact squared-norm identities replace global norms by F,H. No indicator derivative, global raw L² premise, derivative convergence assumption, or new existential coefficient is introduced. Existing local-L² compact-test integrability lemmas justify the raw integrals. The result does not provide TT or mixed derivatives, full joint H², an effective witness-selection algorithm, or an analytic approximation theorem.

Evidence: source `lean/LocalWeakGrushinExplicitOneStepLocalData_v1.lean`, SHA-256 `681116f2bb1deb6f75d35408a0bd2296713a9044fc4b36dc87fd7c9853fe9456`; strict receipt `audits/formal_semantics/20260910T183356_383774Z/receipt.json`, SHA-256 `776294ff928788c3f3e94a8cabb9d67d9440891901dc2c88167d8887dda870fe`. The checkpoint records exact compile/source/object/audit hashes. First compile and strict audit passed; all sessions are consumed. The pinned development cache was reused. This theorem was not part of the earlier v20 desktop snapshot.

The user priority change now defers further regularity formalization and isolated rebuilds. The next task is the adversarial review of the OPEN dictionary approximation lemma; its outcome must determine whether this regularity result is actually required. Full Theorem T remains unverified.

Frozen reference: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
