> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of the direct Grushin factorial recurrence

Evidence category: independent mathematical paper review, not formal proof.

Reviewed artifact: `GRUSHIN_FACTORIAL_RECURRENCE_v1.md`.
Final SHA-256:
`5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594`.

The root agent independently read the complete draft, with particular focus
on R13–R25, and reported that the index regroupings, cutoff annulus weights,
coefficient counts, zeroth-order potential saving R17, scaled recurrence,
source bound, finite geometric induction, H7 pointwise embedding and
factorial constants check. No mathematical defect was found in the main R2
factorial estimate.

One wording correction was requested and made before sealing. The draft's
phrase about a holomorphic extension retaining the same bound could suggest
the real sup bound held throughout the full open complex radius. The final
statement gives the exact geometric bound

\[
 C_*S/(1-A_*\|z-z_0\|_1),
\]

and hence (2C_*S) on the half-radius neighborhood. The real derivative
estimate and its constants did not change.

During construction the exact finite checker also caught an arithmetic
error in the author's first draft: the six correct group counts sum to 498,
not 598. The earlier overestimate would still have given conservative norm
constants, but the cardinality claim was wrong. The current theorem and
checker consistently use the exact 498. Neither draft correction affected
a frozen or previously sealed artifact.

The auxiliary integer checks pass, including 314,721 cost-removal checks,
136,161 comparisons with the printed union, 129,600 componentwise principal
regroupings, 316,740 cutoff outer-norm memberships, 1,032 finite geometric
identities and 257 factorial-shift inequalities. These finite checks do not
prove the infinite analytic assertion; the mathematical proof is the
reviewed text.

The accepted scope is the explicit uniform operator lemma for

\[
 -\Delta_y-c|y|^2\Delta_t+B,
\]

given actual weak equation, common analytic coefficient/source bounds and
H12 initialization. No smallness of the bounded potential is needed. The
physical KS pullback, distance descent, boundary compatibility and all
continuum spectral and algorithmic obligations remain separate. This review
does not convert paper evidence to kernel verification.
