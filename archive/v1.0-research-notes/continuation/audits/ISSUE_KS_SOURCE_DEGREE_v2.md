> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

ISSUE ID: KS_SOURCE_DEGREE_001_v2
DISCOVERY DATE: 2026-09-10 UTC; 2026-09-09 America/New_York
FROZEN FILE: helium_research/sources/regularity_fournais2009_0806.1004.pdf
FROZEN SHA-256: 1d4e7195084f15c6fd59e1fa0df083dc76d85334ad222aadea5e94a38aecd848
LINE / THEOREM: Primary arXiv:0806.1004v1, printed p. 20, equation (4.41), within Proposition 4.4. Frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; annotated tag theorem-t-proof-freeze-2026-09-09.
SEVERITY: FALSE CLAIM
DESCRIPTION: This is a new disposition entry for immutable ISSUE_KS_SOURCE_DEGREE_v1.md, SHA-256 ff68ffd8925a5056c74bdc2df16a788d5a4f9c6ff7e49ba41114016c1cf6786c. The source's degree-(n−1) polynomial estimate with radial power n is literally false, as shown by the analytic lift |y|² descending to B=1. The source's headline analytic-plus-distance theorem is not refuted.
DOWNSTREAM DEPENDENCIES: Frozen KS_SOURCE_AUDIT.md and RWA_THEOREM.md invoke the quantitative descent. The replacement now proves that step directly, conditional on an actual uniformly bounded holomorphic KS lift. Physical regularity, subsequent distance invariance and compatibility, spectral identification and formal verification remain separate.
PROPOSED CORRECTION: Use the completed direct polynomial construction: transform to z and conjugate variables, retain balanced degrees, pair z_i w_j, substitute the four linear generators in (X,r), reduce r²=X·X, and sum the resulting degree-n and degree-(n−1) polynomials. The coefficient norm grows by at most 32^n, giving explicit common complex radii, amplitudes and all derivative bounds. Degree zero and the constant term of B are handled explicitly.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/KS_QUANTITATIVE_DESCENT_v1.md
CORRECTION SHA-256: 17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f
STATUS: REPAIRED AT PAPER LEVEL by a direct constructive algebraic proof. Independent root review KS_DESCENT_ROOT_REVIEW_v1.md has SHA-256 e28143d4e854f48482848dae5ebc304392e48cf0bfb61b4b08f679425c2799ed. Exact Gaussian-rational finite reconstruction checks pass. No Lean or continuum algorithm claim is made. The initial issue and the source PDF remain unchanged.
