> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Analytic dependency audit, version 1

Audit date: 2026-09-09. This report records an independent paper and primary-source review. It is not a Lean verification, a proof that every upstream premise is discharged, or a novelty assessment. No status is upgraded merely because this review found no counterexample.

The core RWA argument has a substantive quantitative proof route. Within the scope inspected here, no concrete false claim or fatal gap was established. In particular, the frozen proof does not infer uniform factorial regularity from qualitative analyticity: it supplies the missing common estimate and finite initialization before applying the published factorial recurrence. The remaining formalization obligations are substantial and are listed below.

## Preservation and exact coverage

All frozen paths in this report are relative to `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. The directory named without the timestamp suffix was not a write target. Every new file from this audit is under `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/analytic/`.

[frozen_coverage.json](frozen_coverage.json) records the complete file list, line counts, exact frozen SHA-256 values from the manifest, recomputed matching hashes, and the precise PDF reading scope. The following local texts were read in full:

- `RWA_REPORT.md` and `CORRECTION_PROTOCOL.md`.
- `rwa_proof/RWA_THEOREM.md`, `UNIFORM_ANALYTIC_AUDIT.md`, `KS_SOURCE_AUDIT.md`, `RESOLVED_SOURCE_AUDIT.md`, `FOCK_SOURCE_AUDIT.md`, `REMAINDER_EQUATION.md`, `EXTERIOR_ANALYTIC_ATTEMPT.md`, and `EXTERIOR_ANALYTIC_AUDIT.md`.
- `dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md` and `EXTERIOR_CONSTANTS.md`.
- `rwa_proof/audit_reduced_identities.py`; this frozen script was **not executed**, because it writes its report adjacent to its own filename.

The archived Grušin PDF was read visually at printed pages 155–156 and 179–183. Its SHA-256 is `c5901af60d30b3a41a7e4a62576cfd1689bcd11ce7097c84299c3077534da93e`. A full text extraction and rendered images of the inspected pages were created externally for review. This does not mean the entire 31-page paper and its cited proofs were independently re-proved.

The local coverage is analytic. The proofs of ground-state existence, spectral separation, global dictionary approximation, moment algorithms, and bit complexity are separate audits. Assertions in the local files about those results remain dependent on those audits.

## Source applicability

1. Fournais et al., *Sharp regularity results for Coulombic many-electron wave functions*, Theorem 1.1: the inspected theorem gives the explicit cusp/log factor with a locally C1,1 remainder. For the physical kinetic normalization, `phi(y)=psi(y/2)` has source energy `E/2`. Substitution gives the frozen coefficient `Z(2−pi)/(3pi)`; the additional quadratic term proportional to `log 4` is smoothly absorbed. No all-order bound follows from this theorem alone. [Primary source, Theorem 1.1](https://arxiv.org/pdf/math-ph/0312060).

2. Fournais et al., *Analytic structure of many-body Coulombic wave functions*, Theorem 1.4, §2.2, Lemma 4.3 and Proposition 4.4: the inspected statements and proof passages concern isolated pair collisions. The distributional KS transformation applies to the physical local H2 solution. The descent uses the actual pullback and its common geometric Taylor bounds. The source's quantitative real-polynomial estimates support common complex bounds after a fixed radius shrink; no derivative-dependent shrink is necessary. Simultaneous collisions are excluded from the pair theorem. [Primary source](https://arxiv.org/pdf/0806.1004).

3. Grušin, Theorem 5.1 and Proposition 5.1: the inspected class, frozen-model conditions, weighted derivative index sets, and recurrence match the specialization in the frozen uniform audit. The published recurrence accepts a common compact-support estimate, common analytic coefficient/source bounds, and finitely many initial weighted norms. It does not assert the physical RWA statement. The parameter uniformity is a local argument supplied in the project and checked below. [Primary English paper](https://www.mathnet.ru/php/getFT.phtml?jrnid=sm&paperid=3054&what=fullteng).

The separate [bounded literature review](literature_review.md) checks the four principal alternative regularity sources, Morgan's abstract, Demkov–Ermolaev's recurrence and the displayed low-order Liverts–Krivec coefficients. Its explicitly uninspected references retain that status. The review found no source that by itself discharges physical RWA. This is not evidence of novelty, nor a claim that no later literature resolves a related question.

## Checks on the core quantitative argument

### Physical extraction and amplitude

In `dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md`, equations (P1)–(P4), the extraction calculation is consistent. For `b=q log rho²`, its Hessian grows only logarithmically; multiplication by `Phi−Phi(0)=O(rho)` gives bounded second derivatives. The nonlinear exponential remainder has still smaller second derivatives. Rotation invariance eliminates the first derivative at the origin. These arguments establish the stated finite-order consequence from the source theorem and symmetry assumptions, without requiring a full physical Fock series.

The constant-subtracted equation (R2) in `rwa_proof/RWA_THEOREM.md` has the correct sign:

\[
(-\tfrac12\Delta+\varepsilon V-\varepsilon^2E)
\frac{\psi(\varepsilon X)-\psi(0)}{\varepsilon}
=(-V+\varepsilon E)\psi(0).
\]

Local Lipschitz continuity controls its amplitude on a fixed normalized shell. It supplies no high derivatives; these enter at the operator step.

### KS normalization and maximal estimate

The nuclear chart multiplication factor is `8|y|²`; the electron-pair factor is `4|y|²` after `X=x1−x2`, `t=(x1+x2)/2`. Thus the principal operators in (R3) and (R5) are respectively `−Delta_y−4|y|² Delta_t` and `−Delta_y−|y|² Delta_t`. The displayed potentials and energy factors are consistent.

For `P_c=−Delta_y−c|y|² Delta_t`, let `omega=sqrt(c)|xi|` after Fourier transformation in `t`. The four-dimensional oscillator has lower bound `4 omega`. Writing `A=−Delta_y+omega²|y|²`, integration by parts gives

\[
\|A v\|^2=\|\Delta_yv\|^2+
\omega^4\||y|^2v\|^2+
2\omega^2\||y|\nabla_yv\|^2-8\omega^2\|v\|^2.
\]

The last term has absolute value at most `||Av||²/2`. This proves the sufficient constants in (U2)–(U4). On a fixed containing box, Poincaré and the energy identity control zero and first orders. All terms of the finite weighted norm are then controlled with one constant. Absorption of the `O(epsilon)` potential requires one upper bound on `epsilon`, and not an order-dependent bound. This supplies the common version of source equation (5.5).

The finite bootstrap is legitimate at the paper level: cutoff commutators involve the energy-controlled `D_y v` and `|y|D_t v`; tangential differentiation commutes with the principal operator; each finite reserve of tangential derivatives pays for the later elliptic recovery of derivatives in `y`. Distributional smoothness is used to justify differentiation, while the quantitative estimates supply the common norms. This should be formalized using weak estimates or regularization, not by treating a qualitative smoothness theorem as a quantitative bound.

### Exact recurrence initialization

At frozen `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md:263`–`289`, the claimed specialization is correct. Grušin's printed page 180 defines, for `m=2, delta=1`, the derivative pairs by

\[
\mathcal R_r^1=\{(\alpha,\beta):|\alpha|\le4,
\ 2|\alpha|+|\beta|\le r\},\qquad
\mathcal R_r^2=\{(\alpha,\beta):|\alpha|\ge4,
\ |\alpha|+|\beta|\le r-4\}.
\]

For `r<=r0=8`, the outer weighted norm adds at most two derivatives to at most eight. A common H12 bound therefore suffices for the starting norms. Printed equations (5.21)–(5.23) use exactly these common inputs. The recurrence supplies factorial bounds after a fixed embedding and Stirling estimate; the bootstrap alone is not used to claim analyticity. This verifies the important logical passage in `rwa_proof/RWA_THEOREM.md:154`–`188` at the paper level.

### Descent and boundary geometry

The analytic-plus-distance decomposition is unique as a germ at a collision: restricting to each line through the collision, continuation from positive to negative line parameter forces both coefficients to vanish in a zero decomposition. This gives separate rotation invariance. At a collinear representative, SO(2) invariance leaves powers of `w=x²+y²`. The coefficient of `w^m z^j(s−s0)^ell` equals the coefficient of `x^(2m)z^j(s−s0)^ell` after setting `y=0`, so a common Cartesian polydisc bound gives a geometric, not factorially worsening, conversion.

A minor detail useful for a formal proof is that a real homogeneous polynomial estimate from KS descent can be converted to coefficient estimates uniformly in its degree. For a degree `k` homogeneous polynomial, the polarization bound for the associated multilinear map is at most `k^k/k!` times its unit-ball bound. Expanding in three Cartesian coordinates adds at most `3^k`. Thus a fixed further radius shrink yields a common holomorphic bound. This fills a standard transition implicit at frozen `RWA_THEOREM.md:215`–`224`; it is not a counterexample to the theorem.

All three nonvertex axes and all three open faces are assigned correctly. Pair-collision sets are disjoint on the normalized two-electron shell. The rational and square-root coordinate conversions have separated denominators in the relevant charts. Fixed smaller cores with retained larger neighborhoods justify the finite-cover common radius. The final scaling differentiates at fixed `epsilon` and correctly introduces `epsilon^(−|nu|)` only.

### Reduced equation and physical tails

The perimetric metric, drift, determinant and logarithmic contractions in `REMAINDER_EQUATION.md` are consistent with direct Cartesian calculations. In particular `q=c(S−c)−ab`, `Delta(q log T)=16q/T`, and the powers in (PDE11) are correct. The degenerating face metric cannot be used as an ordinary elliptic operator through its boundary. The frozen proof correctly returns to physical charts.

The IMS tail proof uses `eta1=r/rho`, `eta2=s/rho`, and `sum |grad eta_i|²=rho^(−2)`. Its lower bound, weighted eigenfunction identity, and constants `97/2048`, `159/2048`, and `K0=161*3^32/159` check. The passage from weighted first derivatives to H2 uses the actual domain identity. In `EXTERIOR_CONSTANTS.md`, the graph-to-H2 estimate and inverse-weight multiplication matrix give the displayed sufficient constants. These are physical-function tails and by themselves say nothing about extrapolation of trial polynomials.

### Exterior analyticity

The global real amplitude estimate uses a bounded-coefficient conjugated equation and Moser iteration, rather than an invalid H2-to-L-infinity embedding in six dimensions. The exponents `p_j=2(3/2)^j` have sums `sum 1/p_j=3/2`, `sum j/p_j=3`; the displayed coarse product bound is sufficient.

The translated KS charts retain common spectator separation. The frozen electron-pair center bound has already been changed to `D/4`, which is sufficient for projected exterior centers. The unbounded exterior is handled by fixed chart sizes and coefficient bounds, not a compactness claim. The algebraic changes `|Delta z|<=9 delta` and `|Delta w|<=102(1+S)delta` justify the stated polynomial radius loss. In §5, bounded overlap of local cutoff supports prevents an exponential dependence on their number; the Chebyshev tail power fourteen is consistent with integrating `t^13 exp(−bt/2)`.

## Status and exact remaining obligations

The established primary results include local factorization, isolated-pair analytic structure, and the stated analytic-hypoelliptic recurrence. The project-specific uniform specialization, invariant-coordinate descent, and exterior estimate have survived this bounded paper audit. They remain unverified in Lean. Calling these physically false merely because Lean is absent would be unwarranted; calling them fully machine verified would also be wrong.

For a full Lean theorem, the following must still be encoded and proved: the actual Coulomb operator and its domain; source regularity in the correct function spaces; weak KS pullback; the oscillator and localized maximal estimates; weak-to-smooth initialization; the factorial recurrence with all constants and domain losses; quantitative analytic descent and invariant germs; closed-octant compatibility; and weighted tail estimates. Approximation, residual transfer, spectral certification, executable rational computation, termination and the bit-cost model are additional dependencies outside this report. A theorem that accepts these as mathematical premises remains conditional. An assumed structure packing these conclusions would not discharge them.

No erratum is opened by this report because no definite frozen mathematical error was established in its reviewed scope. An optional strengthening is developed separately as a conditional candidate in `RWA_QUADRATIC_WEIGHT_CANDIDATE_v1.md`. Neither it nor the present audit establishes novelty or changes a frozen status label.
