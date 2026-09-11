> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual compact Grushin estimates — formal checkpoint v1

Let T be any finite-dimensional Euclidean spectator space, c >= 0, and G : R^4 x T -> C be C-infinity with compact support. Define P_c G = -Delta_y G - c |y|^2 Delta_t G. With product Lebesgue measure, the compiled theorem proves simultaneously:

1. 16 c sum_j integral |D_tj G|^2 <= integral |P_c G|^2.
2. integral |Delta_y G|^2 + integral |c |y|^2 Delta_t G|^2 <= (3/2) integral |P_c G|^2.
3. 2 c sum_i sum_j integral |y|^2 |D_tj D_yi G|^2 <= (3/2) integral |P_c G|^2.

These are actual Frechet directional derivatives in standard orthonormal bases. The c=0 case and the zero-dimensional spectator space are included. All integrability used in the proof is discharged. No differential estimate is assumed in the final theorem.

The actual partial Fourier transform uses exp(-2 pi i <t,xi>). Each frequency gives the four-dimensional harmonic oscillator with a = 2 pi sqrt(c) |xi|. Its proved lower bound and weighted cross identity give 16 and 3/2. Joint Plancherel and finite-sum integral transfer return the estimates to configuration space. Weighted Plancherel needs only continuity of the y-weight, so using |y| does not presume smoothness at zero.

The accompanying checkpoint records eighteen modules and the mechanically counted declarations, current source/object hashes, and full expanded-statement and axiom receipts. Only propext, Classical.choice and Quot.sound occur. Pinned library/prior-audit and continuation object caches were reused. An isolated source rebuild of these new modules is not claimed here.

This proves estimates for compact smooth functions. Local distributional gain, quantitative initialization, factorial recurrence, physical solution analyticity, and other collision strata remain separate obligations. No numerical solver, complexity theorem, novelty claim, or full Theorem T is asserted.

All work is new continuation source. Frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Frozen relative path rwa_proof/RWA_THEOREM.md has SHA-256 d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09; RWA_REPORT.md has SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066. Historical bytes remain unchanged.
