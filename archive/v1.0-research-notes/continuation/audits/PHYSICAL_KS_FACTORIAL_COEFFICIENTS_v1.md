> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Physical KS factorial coefficient bounds

Evidence: Lean theorems compiled and exact statements/axiom dependencies audited with the pinned dependency cache. This is not an isolated dependency rebuild or an executable constant-evaluation algorithm.

For any fixed compact subset K of the actual nuclear KS coefficient patch (any finite N and selected electron i), and for fixed real charge Z and energy E, there exist C,A >= 1 such that, for every epsilon in [0,1], every point q of K and every derivative order k,

- the actual coefficient b_epsilon(q) = nuclearKSPotential i Z (epsilon E) q has operator derivative norm at most C A^k k!;
- the actual physical scaled coefficient B_epsilon = epsilon b_epsilon has derivative norm at most epsilon C A^k k!;
- the normalized forcing -a0 b_epsilon has derivative norm at most C A^k k! |a0|, for every complex a0.

The same theorem holds for the actual two-electron pair KS coefficient on its genuine pair patch. The nuclear/pair energy terms are exactly -8 epsilon E |y|^2 and -4 epsilon E |y|^2 inside b_epsilon, respectively. The singular fiber y=0 is included wherever allowed by the regularized coefficient patch. No inverse epsilon or replacement Hamiltonian occurs.

The constants are chosen before epsilon, q, k and a0. The proof uses one summable binomial majorant for all translated multilinear power-series coefficients, the full permutation formula for actual Frechet derivatives, and a finite cover of K. It does not promote order-by-order smooth compactness to an all-order bound. The source norm follows by composition with the actual constant-vector scalar multiplication map.

A further formal result bounds every actual ordered mixed Y/T coordinate word of total length k by the same majorant. On any measurable S subset K, the actual squared L2 forcing budget is (C A^k k!)^2 |a0|^2 volume(S). The existing smooth mixed source-word theorem provides the genuine weak links; these new statements concern the corresponding norms. Compactness supplies finite measure even for the arbitrary-N nuclear case.

Root read the exact four final source files and the actual imported derivative/source-budget arguments used. An independent focused review covers the affine and physical coefficient modules; it found no quantifier, factorial, scaling or sign defect. Strict audits cover all eleven new local declarations (including the translated-majorant definition), with only propext, Classical.choice and Quot.sound. The source scanner required a narrow new version to recognize the pinned infinite sum/product prime tokens; all old bytes and checks remain preserved.

Limits: C,A may depend on N,i,Z,E,K and are not evaluated. A common annular region supplies uniformity in chart centers only after instantiation. These are coefficient and forcing bounds, not an all-order bound for the physical eigenfunction. The Grushin weighted maximal estimate, genuine differentiated weak equation, quantitative recurrence, descent and physical distance germs remain on the critical path. Full Theorem T is unverified; no new energy interval or bit-complexity theorem is asserted.

Historical target: frozen relative path rwa_proof/THEOREM_T_COMPOSITION.md, SHA-256 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Frozen artifacts and all passed sources remain unchanged.
