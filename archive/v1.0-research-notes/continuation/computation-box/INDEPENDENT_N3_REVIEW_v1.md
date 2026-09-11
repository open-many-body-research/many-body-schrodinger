> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the N=3 signed-exchange stage

Date: 2026-09-09. Evidence: **paper/code review and finite independent exact checks**, not Lean verification. Reviewed source hashes are:

| Source | SHA-256 |
|---|---|
| `exact_box_v1.py` | `f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58` |
| `exact_two_electron_stage_v1.py` | `8f5688e38d89b9cf75ebb8257edf339c12a1bb7a231d71f638e8978246e174b4` |
| `exact_lithium_stage_v1.py` | `9916119d0868c3fd82ea432036939bd9b845434a9bb52a4391567513b97ad561` |
| `LITHIUM_EXCHANGE_STAGE_v1.md` | `371a3c0935b5e12e87159dcfca683957cf16e49606a601ab66a81f929f8717dc` |

The frozen baseline remains `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`, SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. This new finite-stage computation does not implement or revise the frozen two-electron dictionary.

No invalid sign, spin factor, complement coefficient, clipping direction, or interval-grouping operation was found in the reviewed source. Its target is the actual N=3 uncut Coulomb Dirichlet infimum on Ω³, Ω=(-2R,2R)^3, with form domain H¹₀(Ω³;C⁸) intersected with simultaneous spatial/spin antisymmetry. The continuum form/spectral identification remains a paper dependency. The fixed rank-one computation does not establish arbitrary-precision convergence or a complete three-electron theorem.

## Slater coefficients and the degenerate complement

The three occupied orthonormal spin orbitals are φ₁↑, φ₁↓, φ₂↑, with φ₁=φ₁₁₁ and φ₂=φ₂₁₁. Expanding the normalized determinant and integrating a spectator particle gives the sum over occupied orbital pairs of a direct term minus the exchange term weighted by the spin scalar products. The φ₁↑/φ₁↓ pair contributes J₁₁; the two φ₁/φ₂ pairs contribute 2J₁₂, but only the pair with two up spins contributes exchange. Thus total pair energy is exactly J₁₁+2J₁₂−K₁₂, with one exchange subtraction. The nuclear contribution is −Z(2ν₁+ν₂), and the kinetic energy is (3+3+6)π²/(32R²).

For the free Dirichlet kinetic operator the lowest spatial level has two spin copies, and the next level has three spatial orbitals and two spins. Three fermions must occupy both lowest spin orbitals and one of these six next-level orbitals to minimize kinetic energy. The free ground eigenspace consequently has dimension six and energy 12π²/(32R²). The source's rank-one trial projection commutes with the kinetic operator, but its complement still contains five vectors at the same energy. The chosen Q lower bound 12π_lo²/(32R²) is valid. Importing a next-energy threshold as though this eigenspace were simple would be invalid; the code does not do that.

The Coulomb multiplication bound B=M(3Z+3) is conservative for the three nuclear and three pair terms. The P/Q Young estimate then gives min(compression_lower−η, Λ−B−B²/η) on the clipped continuum form. Neither the selected spin orientation nor this weak kinetic lower bound restricts the target to one spin sector.

## Mixed direct and signed exchange grouping

For the mixed direct J₁₂ integral, one coordinate uses different sine-square probability arrays. Its nonnegative signed-difference weight is s_d=Σ_j w₁,j w₂,j−d. Equality s_−d=s_d follows by reflecting both labels, because each sine-square array is reflection-even. Swapping the unequal arrays alone would not prove it. The source and final document use the correct reflection argument.

The exchange factor in the first coordinate is φ₁φ₂. It has one node at the midpoint, so even J makes its sign constant on each open cell. The code determines this sign from the cell's known position, not from the sign of an uncertain numerical interval. Multiplying the overlap enclosure by the known sign and intersecting with the nonnegative half-line gives an enclosure for its exact magnitude.

Each original six-dimensional cell pair now has a fixed exchange-integrand sign. For every absolute cell-label difference, the code sums positive masses and negative magnitudes separately. The other two coordinates use nonnegative identical-density weights. The usual relative-distance extrema enclose the potential throughout every contributing cell product. Multiplying that potential interval into each nonnegative sign group and subtracting the two accumulated intervals is therefore sound. Positive and negative groups individually have the stated signed-difference symmetry, so the factor 2 for each nonzero coordinate difference is correct.

There is a concrete reason not to collapse the signed masses first. A group containing mass +1 at potential value 1 and mass −1 at potential value 2 has weighted integral −1. Its total signed mass is zero, so multiplying that zero by the potential range [1,2] would incorrectly return zero. Keeping the two nonnegative magnitudes gives [1,2]−[1,2]=[−1,1], which includes the true value. The implementation preserves exactly the information this example requires.

The code does not assume K₁₂≥0 for the clipped interaction. Pointwise positivity of a kernel alone does not prove positivity of its quadratic integral on a signed function. It intersects only the total J₁₁+2J₁₂−K₁₂ with the nonnegative half-line. That intersection is valid because this exact total is the expectation of a sum of nonnegative pair multiplication potentials in the full normalized determinant.

## Restoration and common upper bounds

For N=3 the absolute form clipping estimate is |q−q_M|≤δT, δ=(2Z+2)/M. The pair-only contribution is at most 2T/M, and nuclear unclipping lowers the energy. Thus the displayed trial obeys q[Ψ]≤q_M[Ψ]+2T_trial/M, and the computed `trial_upper` bounds both true and clipped minima.

The additional common bound 14 is valid. The pair estimate for N=3 is at most 2√(6T)≤T+6, while T_trial=12π²/(32R²)<15/4 for R≥1. Dropping attraction gives both trial forms at most 2T_trial+6<27/2<14. Hence U=min(14,trial_upper) is a common upper bound.

Both forms satisfy q,q_M≥T/2−3Z². Their normalized minimizing states therefore have kinetic energy at most K₀=2(U+3Z²). Evaluating each form at the other form's minimizer gives both directions of |λ−λ_M|≤δK₀. Alternatively, approximate minimizers give the same result after their errors tend to zero. The final restored lower/upper endpoints have the correct directions. The elementary lower bound −3Z²/2 is valid for both forms by nuclear square completion and nonnegative pair repulsion. Full-space zero extension is at H¹ form level, and the upper intersection with zero follows from distant dilated fermionic trials. No binding or attainment in full space is used.

## Independent executed checks

`independent_n3_checks_v1.py` explicitly enumerates every six-dimensional pair of physical cells. It forms relative-distance bounds directly from the two cell endpoint intervals, integrates the mixed direct weights without the difference grouping, and sorts each exchange cell product by its known sign. It does not call the grouped-weight implementation. It writes JSON only to stdout:

```sh
python3 -B THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/computation/box/independent_n3_checks_v1.py
```

The exclusively created receipt `independent_n3_checks_v1.json` records exact equality of all four intervals (mixed direct, exchange, positive exchange part, negative exchange magnitude) for J=2 and J=4 at (R,M)=(1,3) and (2,1/32): 8,320 explicit six-dimensional cell pairs in total. Constant clipping gives the independently known direct value M and exchange value zero; all intervals contain these exact values. The generic cancellation counterexample above is checked as well.

These tests share the previously reviewed interval primitives. They test normalization, reflection, signs, cancellation handling and exact grouping; they are not a separate arithmetic kernel, formal proof, or general convergence theorem. Saved stage intervals, their replay results, timings and source-only reproduction belong to the execution report. This review does not relabel a loose interval as an improved physical lithium estimate or infer wavefunction accuracy from energy endpoints.
