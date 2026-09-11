> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

ISSUE ID: KS_SOURCE_DEGREE_001_v1
DISCOVERY DATE: 2026-09-09
FROZEN FILE: helium_research/sources/regularity_fournais2009_0806.1004.pdf
FROZEN SHA-256: 1d4e7195084f15c6fd59e1fa0df083dc76d85334ad222aadea5e94a38aecd848
LINE / THEOREM: Primary arXiv:0806.1004v1, printed p. 20, equation (4.41), within the proof of Proposition 4.4. Frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; annotated tag theorem-t-proof-freeze-2026-09-09.
SEVERITY: FALSE CLAIM
DESCRIPTION: The displayed estimate bounds a homogeneous polynomial of degree n−1 by a fixed constant times |x|^n. This is false for a nonzero such polynomial near x=0. The admissible analytic pullback u(y,t)=|y|², corresponding to psi(X,t)=|X|, has at n=1 a descended second coefficient equal to 1. Equation (4.41) would give 1≤C|x|, which fails as x tends to zero for every finite C. The printed exponent was confirmed in the exact frozen PDF by rendering and visually inspecting p. 20, in addition to the primary arXiv PDF and HTML text. The issue concerns this displayed estimate, not the existence theorem for analytic-plus-distance descent.
DOWNSTREAM DEPENDENCIES: Frozen rwa_proof/KS_SOURCE_AUDIT.md invokes the quantitative proof of Proposition 4.4; frozen rwa_proof/RWA_THEOREM.md section 5 uses its uniform coefficient descent. The continuation's weak H12, factorial recurrence and removability lemmas do not depend on equation (4.41). No counterexample to the headline descent theorem, physical RWA, or the conditional dictionary theorem follows from this source typo.
PROPOSED CORRECTION: Replace the radial degree on the right by n−1 for the second coefficient, treat n=0 separately for the first coefficient, and establish a quantitative common complex radius by explicit coefficient control and geometric summation. Develop this as a new direct descent proof in KS_QUANTITATIVE_DESCENT_v1.md. Record its completed hash in a new issue entry; do not modify this entry or the primary PDF.
CORRECTION FILE: PENDING: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/KS_QUANTITATIVE_DESCENT_v1.md
CORRECTION SHA-256: PENDING
STATUS: Confirmed literal false estimate; straightforward degree correction identified; complete quantitative continuation proof in progress. This immutable issue does not downgrade the headline source theorem to false.
