> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Bounded independent primary-source review of the resolved-regularity and Fock audits

Review date: 2026-09-09. Status: completed for the expressly identified passages below; not a complete literature survey, a Lean proof, or an audit of the separate direct RWA argument.

## Frozen provenance

The files read in full were:

| Frozen relative path | SHA-256 recorded in `FREEZE_MANIFEST.json` |
| --- | --- |
| `rwa_proof/RESOLVED_SOURCE_AUDIT.md` | `f0f0b5e07fda02a7ccb817b7b40f8359fe571a67eb48eca1741825409214b85e` |
| `rwa_proof/FOCK_SOURCE_AUDIT.md` | `22afddf6ece73481c32b98d03e8067ebe393cd28f09569f1e7de4b46f30e10ce` |

These are under `THEOREM_T_FREEZE_2026-09-09_212604/`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. `CORRECTION_PROTOCOL.md` was also read. No frozen bytes were changed. The user's separately named `THEOREM_T_FREEZE_2026-09-09/` was not used as a write location.

## Findings

No concrete mathematical discrepancy was found in the **source-applicability statements examined here**. This does not validate every assertion in either frozen file. In particular, the sentence in the Fock audit asserting that a separate direct RWA proof was subsequently completed is outside this review; it must be audited independently.

1. **Ammann–Mougel–Nistor.** Inspected the 45-page arXiv v3, dated 27 February 2023 on the title header, introduction and Theorem 1.1 on page 3. The theorem has the intersection-closed finite subspace family, smooth coefficients on the resolved compactification, and distributional equation off the collision union described in the frozen audit. Its conclusion is weighted Cartesian Sobolev membership for every multi-index, using the clipped distance to the collision union. It does not state a factorial bound uniform in order. The two-electron sign and diagonal-distance conversion in the frozen audit are correct: the coefficient `-sqrt(2)` divided by diagonal-plane distance `u/sqrt(2)` gives `-2/u`. The frozen summary is accurate for this preprint statement. Agreement with the published version was not independently checked. [Primary preprint, Theorem 1.1](https://arxiv.org/pdf/2012.13902v3).

2. **Fournais–Sørensen.** Inspected the 46-page PDF, whose first-page date reads 3 September 2018, Theorem 1.1 and Corollary 1.2 on pages 3–4, and definitions of the collision distances. The theorem expressly permits the constant to depend on the multi-index. Corollary 1.2 gives the fixed-order power `lambda^(1-|alpha|)` in terms of a local supremum of the solution. It does not itself bound that constant factorially. The frozen rescaling is correct: if the physical kinetic coefficient is `-1/2`, then `phi(y)=psi(y/2)` satisfies the paper's kinetic convention with energy divided by two. Collision-distance control cannot simply replace the requested weight `S`, which remains positive at nonvertex pair collisions. No discrepancy was found in the frozen description of these statements. [Primary preprint, Theorem 1.1 and Corollary 1.2](https://arxiv.org/pdf/1803.03495).

3. **Maday–Marcati.** Inspected the 19-page preprint, system (3), assumptions (4)–(6), Theorem 1, and Corollary 1 on pages 3–4. The theorem actually includes the uniqueness hypothesis quoted in the frozen audit; this was not added by the audit. The spatial dimension is two or three, singularities are isolated points with a separation condition, and the operator is the displayed coupled Laplacian/Poisson system. The all-order bound is factorial, with one constant independent of the multi-index. This establishes an appropriate isolated-singularity theorem under its own premises. It does not establish the asserted regularity for the correlated six-dimensional two-electron equation or its degenerate rotational reduction. The frozen applicability distinction is justified. [Primary preprint, Theorem 1 and Corollary 1](https://arxiv.org/pdf/2010.06923).

4. **Costabel–Dauge–Nicaise.** Inspected the 54-page PDF, problem (6.3), Definitions 6.3–6.4, Assumption 6.5, and Theorem 6.8. The model operators and homogeneous face conditions form the stated elliptic system with homogeneous constant coefficients. Theorem 6.8 requires the edge estimates in Assumption 6.5 and initial weighted first-order membership. The analytic conclusion uses anisotropic weighted seminorms and uniform factorial order control. Thus the source supplies a genuine analytic regularity shift for the specified boundary problem; it does not identify the reduced Coulomb problem with that boundary problem. Applying it here would require separately proving operator, boundary-condition, and initial-estimate compatibility and the conversion from its weighted derivatives. The frozen audit correctly declines that inference. [Primary preprint, §§6.1–6.2](https://arxiv.org/pdf/1002.1772).

5. **Morgan.** Read the primary publisher abstract only. It explicitly distinguishes pointwise convergence for representable S-state solutions, without an infinity boundary condition, from the question of representation of the decaying physical eigenfunction. The frozen abstract-level description is faithful. The abstract supplies neither the requested uniform angular analytic estimate nor a physical-series identification theorem. This is a statement about the inspected abstract and the paper's stated scope, not a claim that the issue has remained unresolved in all subsequent literature. Full-text theorem hypotheses were not verified. [Primary publisher abstract](https://link.springer.com/article/10.1007/BF00526420).

6. **Demkov–Ermolaev.** Read the accessible three-page primary paper. Equations (2)–(6) develop the recurrence from a series ansatz, and equation (8) accommodates homogeneous potential expansions. The text makes broad validity assertions and refers to omitted analysis and future detailed work. It does not display the all-order norm estimate needed for RWA or uniform analytic control through the reduced collision edges. Its broad prose is not, on its own, a discharged quantitative premise. The frozen distinction between useful recurrence algebra and the missing quantitative input is justified. The original Fock text was not recovered or independently reviewed here. [Primary paper](https://jetp.ras.ru/cgi-bin/dn/e_009_03_0633.pdf).

7. **Liverts–Krivec.** Inspected arXiv v2, equations (1)–(13), the introduction, and its Morgan reference. The displayed low-order coefficients agree with those used in the frozen audit. Direct substitution of the normalized harmonics in equations (12)–(13) gives the quartic expression in frozen equation (F3). Subtracting the product of the linear cusp and quadratic logarithm from the cubic logarithm gives frozen equation (F2). These checks validate conditional algebra on the cited coefficients. They do not identify a physical wavefunction with a full series or bound all angular coefficients in a common analytic neighborhood. The paper's introductory convergence sentence cites Morgan; that sentence cannot strengthen the theorem scope verified in Morgan's abstract. [Primary preprint, equations (1)–(13)](https://arxiv.org/pdf/2209.09053v2).

## Independent algebra checks and limits

For the quartic identity, write `rho^2=r^2+s^2` and `q=(rho^2-u^2)/2`. Then the harmonics in the cited coefficient obey

\[
\rho^4\pi^{3/2}(Y_{40}+\sqrt2Y_{42})
=3\{\rho^4-8r^2s^2+8q^2\}.
\]

The factor three converts the coefficient denominator `540 pi^2` into `180 pi^2`, as in (F3). For (F2), collecting the cusp-conjugation terms leaves

\[
\kappa\rho^3\left[\frac{Z\eta}{2}(1-\xi^2)+\frac{\xi^3}{12}\right]
=\kappa\left[ZS q+\frac{u^3}{12}\right].
\]

These are finite symbolic identities, not a regularity argument. The finite-log compatibility lemma in the frozen file has an explicit common holomorphic-neighborhood hypothesis. Its Cauchy estimate and logarithmic absorption argument were checked on paper and no defect was found. A finite check cannot validate the common-neighborhood or summability assumptions for an infinite physical Fock series.

The resolved many-body result can be applied at fixed electron count only after including the full intersection-closed collision family. At `N=3`, this includes strata such as `x1=x2=0`, with `x3` free. The finite-order theorem therefore has geometric relevance away from total collapse as well; it still does not supply an ordinary reduced-coordinate factorial bound or an approximation/certification theorem. This last observation is a direct consequence of the family definition and the theorem's limited conclusion, not a proposed three-electron theorem.

## Remaining review scope

This review did **not** independently verify the primary theorem text for Ammann–Carvalho–Nistor, Marcati–Rakhuba–Schwab, Flad–Schneider–Schulze, Guo–Babuška, original Fock, or the 2015/2016 coefficient papers. Their frozen summaries have not been upgraded by this report. It also did not assess the published-versus-preprint agreement claimed in the frozen audit, the separate Grushin/KS-based proof, global H² approximation, spectral certification, or complexity.

The result established here is bounded: the inspected primary statements do not already discharge the physical RWA obligation, while the checked low-order logarithmic algebra supplies no contradiction to RWA. Neither a novelty claim nor a theorem status upgrade follows from that conclusion. No new erratum was opened because no concrete discrepancy was found within the inspected scope.
