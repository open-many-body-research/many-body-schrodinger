> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual analytic factorial bounds on compact sets, version 1

Let E and F be real normed vector spaces, with F complete. Let K be a compact subset of E, and let f:E->F be analytic at every point of K (`AnalyticOnNhd` over the reals). There are constants C>=1 and A>=1 such that

\[
\|D^k f(x)\|_{\mathrm{op}}\le C A^k k!
\qquad(x\in K,\ k\in\mathbb N).
\]

The formal result is slightly stronger: the same bound holds on a single neighborhood of K. The derivative is Mathlib's actual `iteratedFDeriv`, represented by a continuous k-multilinear map and equipped with its operator norm. No finite-dimensionality of E, nonempty-set assumption, or pre-existing factorial derivative estimate is required.

The local analytic theorem imported from `PowerSeriesLocalDerivativeBound_v1` derives constants on a ball from a genuine power-series representation. Its proof uses the source series' summable translated-coefficient majorant and the operator-norm estimate for the actual derivatives at the center of the translated series. The constants precede both the ball point and the derivative order. The compactness theorem then chooses a finite neighborhood subcover and takes one plus the finite sums of its local constants. The empty compact set is covered by the same construction.

This composition discharges the local factorial-bound hypothesis of the separately recorded conditional compactness lemma for actual analytic functions. The final hypotheses are compactness, real analyticity near K, the normed-space structures, and completeness of F. They do not assume the asserted derivative bound or replace the derivatives by selected coefficients.

The exact APIs are `analyticOnNhd_compact_factorial_bound_nhds` and `analyticOnNhd_compact_factorial_bound` in `TheoremT.Continuum`. Both final expanded statements compile under the pinned Lean 4.34.0-rc2 environment and pass strict version-6 audits with no printer omissions and only propext, Classical.choice and Quot.sound. The separately sealed local analytic and conditional compactness dependencies are linked by the checkpoint. Existing dependency objects were reused; no isolated source rebuild is claimed.

The constants are existential, selected from analytic data and compactness. This is not an executable extraction algorithm or an effective complexity theorem. Applying it to a physical KS coefficient or wavefunction still requires proving that the actual function is analytic on the indicated neighborhood, as well as any desired uniformity in additional parameters. This general lemma does not by itself establish the original global approximation claim or full Theorem T, and no novelty claim is made.

Frozen project provenance: `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`, SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. All historical bytes remain unchanged; this is a separate formal continuation result.
