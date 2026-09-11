> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exact targets and outstanding proof obligations, version 1

Date: 2026-09-09. This file specifies the continuation of the project. It does not declare its outstanding theorems proved. Existing versions and completed errata are historical records; subsequent work must use new files under `THEOREM_T_POST_FREEZE_WORK/`.

Frozen baseline: `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The report `RWA_REPORT.md` has SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`; the complete referenced local-path inventory is in `FROZEN_DEPENDENCY_INVENTORY_v1.json`. Source coverage and literature-access limits are in the component reports.

## The model must remain fixed

For electron count N, configuration space is R^(3N), spin configurations are `{up,down}^N`, and the Hilbert norm is the sum of the continuum L2 norms of all spin components. Antisymmetry permutes spatial coordinates and spin labels simultaneously. The nucleus is a fixed point of charge Z at the origin, kinetic energy is `−(1/2) sum_i Delta_i`, nuclear attraction is `−Z sum_i 1/|x_i|`, and repulsion is `sum_(i<j) 1/|x_i−x_j|`.

The intended operator domain is the actual spatial weak Sobolev H2 space intersected with the fermionic subspace, and the form domain is H1 intersected with it. Assigning any representative value on collision sets is harmless only after their measure-zero property has been proved. The target energy is `inf spectrum(H_N,Z)`, whether or not attained. A variational-infimum definition is a useful intermediate only with its precise function domain and a separate proof of equality to the spectral infimum; no unknown finite real number is silently assigned to an empty or unbounded numerical range.

For N=2 the exact dictionary is

    V_n^(Z) = sum_(j=0)^floor(n/2) exp(−Z 2^j (r+s)) P_(n−2j)^sym(r,s,u),
    r=|x1|, s=|x2|, u=|x1−x2|.

Here P_d^sym means ordinary polynomials of total degree at most d, symmetric in r,s. Tensor with the unit two-spin singlet. Rational factorial and dyadic column scalings change the coefficient representation, not the span. The raw functions and their L2 lifts must be related, with domain inclusion proved; defining only a finite coefficient matrix does not formalize this dictionary.

N always denotes electron count in new work; n denotes approximation order; p denotes requested energy precision. Use another symbol for the frozen auxiliary `n+2` and for Poisson-window degree.

## Dependency chain and measurable completion criteria

| ID | Obligation | Completion criterion |
|---|---|---|
| F01 | Fermionic continuum Hilbert space | Closed simultaneous-permutation subspace of the actual spin L2 space; completeness, actions and domain preservation proved |
| F02 | Coulomb graph on H2 | Collision nullity, weak derivatives, sliced Hardy and Fourier interpolation; every H2 fermionic input has a unique fermionic Hamiltonian output |
| F03 | Self-adjoint realization | Construct a densely defined unbounded operator from that graph and prove self-adjointness and exact H2 domain, rather than assuming them |
| F04 | Spectral ground energy | Semiboundedness and equality of the operator/form variational infimum to the spectral infimum |
| S01 | Two-electron ground branch | Exact hydrogenic spectrum, Pauli rank-one comparison, rational L,U,beta,g, strict anchor margin, positivity and exchange/rotation symmetry |
| A01 | Physical finite regularity | Actual eigenfunction and cusp/log factorization in the correct weak spaces, normalization and value at the origin |
| A02 | Uniform all-order regularity | Weak KS pullback, oscillator estimate, localization and finite initialization, factorial recurrence with common constants, quantitative descent and compatible boundary germs |
| A03 | Exterior analyticity and decay | Uniform translated charts and actual physical weighted H2 tail, including distant pair collisions |
| D01 | Exact global dictionary approximation | Ordinary shell-polynomial construction, exact windows and node budget, all tails, weak Hessian integrability and one global admissible vector |
| D02 | Residual transfer | Graph/H2 comparison and normalization for the actual operator; no energy-error or H1 rate substituted |
| S02 | Continuum spectral certificate | Spectral-measure or equivalent unbounded-operator Temple inequality on D(H); full spectral identification, not a finite-matrix theorem |
| C01 | Exact moments | Derive physical measure, full Hamiltonian action, moment integrals, constant enclosures and all-order height bounds for the original dictionary |
| C02 | Executable finite solve | Rational matrix bounds, constructive PSD/negative witnesses, common denominators, perturbation and interval-safe acceptance implemented and proved |
| C03 | Effective search and termination | Prove every emitted interval correct, every finite stage terminates, and RATE plus coefficient bounds imply eventual successful stopping |
| C04 | Bit complexity | Operational binary integer/rational cost semantics, operand-size bounds, generation/integration/solve/output cost and stopping-order sum verified |
| T02 | Full two-electron Theorem T | A compiled theorem referring to the constructed continuum operator and verified executable, with F01–C04 discharged; audit its expanded statement and all axioms |

A separately compiled conditional implication is useful, but must explicitly list its undischarged mathematical premises. The present project-specific analytic and cost proofs have paper review evidence; they are not Lean theorems merely because their scalar conclusions compile. The full theorem cannot be assembled by introducing a structure whose fields assert F02–C04.

## Immediate formalization sequence

1. Finish the continuum foundation and exact-dictionary modules, retaining every successful build and failed-attempt log. Prove closure of the fermionic subspace and uniqueness of weak derivatives/graph outputs. Record exactly what is defined and what is proved.
2. Prove the three-dimensional Hardy estimate for compact smooth functions, extend it to H1, and lift it by slicing to the configuration/spin space. Derive `||V f|| <= sqrt(N)(2Z+N−1)||grad f||` and the infinitesimal Laplacian relative bound. These are shared N=2/N=3/general-N foundations.
3. Connect the weak graph to a densely defined `LinearPMap`, prove symmetry, and build the required self-adjoint perturbation theorem. Only after this step identify the ground-energy quantity with an actual unbounded spectrum.
4. Formalize the hydrogenic comparison and continuum spectral certificate; independently formalize exact trial weak derivatives and moments. These branches can proceed in parallel after the common space/domain work.
5. Translate the written uniform-analytic proof into quantified local lemmas. Preserve its oscillator/factorial recurrence estimates and their hypotheses; do not replace them with an analyticity assumption and call the full theorem complete.
6. Implement the rational search with an independently proved instance-dependent precision schedule or the exact frozen schedule. A changed schedule is a new algorithm version. Prove its behavior and bit cost, then compose only proved premises.

The installed pinned mathlib has `Analysis/InnerProductSpace/LinearPMap.lean`, including basic unbounded adjoint, dense-domain and closedness results. Its `Analysis/InnerProductSpace/Spectrum.lean` documents finite-dimensional and compact-operator spectral results. A bounded keyword inspection found no ready Kato–Rellich, Coulomb hydrogen spectrum, KS, or Grušin implementation in `Mathlib/Analysis`. This is a local search result, not a theorem that no formalization exists elsewhere, nor a reason to substitute a bounded finite operator.

## Lithium branch

The lithium milestone supplies the actual N=3,Z=3 model, an explicit spin-sector isometry, an exact rational Slater trial and a quartet exclusion argument. Its paper continuum inputs and rational-execution boundary are identified in `lithium/LITHIUM_MILESTONE_v1.md`.

The next regularity theorem must cover all proper collision partitions on a normalized R9 shell: a nucleus pair, an electron pair, two disjoint pairs, nucleus plus two electrons, and three electrons away from the nucleus. In particular `x1=x2=0, x3!=0` has simultaneous r1,r2,r12 poles. Clearing only one KS pole leaves the others singular. The two-electron isolated-pair theorem does not apply to this model.

The ground has spin 1/2 by the paper energy comparison; orbital L=0 and exact doublet multiplicity have not been established here. An ionization threshold does not exclude discrete excited states and cannot automatically serve as a Temple separator. Establish either a ground-cluster spectral exclusion/complement bound or the gap-free lower mechanism below before claiming a terminating lithium certificate. A Gaussian graph-dense fallback core gives convergence of variational upper bounds, without a precision rate.

## General-N branch

The input class here is finite integer N>=0 and Z>=1, a single infinitely massive point nucleus, and p>=1. Output is a rational absolute ground-energy enclosure of width at most 2^(−p). It does not include arbitrary observables, binding decisions, molecules, external fields, or user-selected finite orbital bases.

`arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md` derives a two-sided full-space/Dirichlet recursion and proposes `BoxEnclose`. The next executable milestone is to implement and prove that routine's clipped-potential integral bounds, sine-Slater enumeration, rational matrix perturbations, PSD bisection, and complement bound. It must return lower as well as upper bounds for the uncut continuum box problem. Only then compose the explicit recursion and prove total requested-precision output.

This route has deliberately poor size growth and supplies no polynomial-in-p or uniform-in-N result. Keep fixed-N computability, fixed-N polynomial precision cost, and growing-N efficiency as separate statements. Track dependence on N,Z,p, constants and any separator. Primary QMA-hardness reductions for supplied finite orbital bases or engineered electric/magnetic potentials restrict broad claims only when those input classes are actually included; they are not automatically hardness results for the (N,Z)-only atom.

## Status discipline

The component paper audits did not establish a fatal flaw in the two-electron proof within their stated scope. That is evidence of review, not a completed formal proof or a novelty finding. One terminology erratum is recorded in `errata/ERRATUM_001_MOMENT_SPAN_v1.md`, with frozen SHA, correction SHA, commit/tag and sealed records. Conditional improvements of a radius schedule or extracted remainder weight remain separate candidate lemmas. No full Theorem T, lithium analogue with polynomial precision cost, or uniform many-electron efficiency theorem is certified by this continuation specification.
