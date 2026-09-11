> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent N=1 bounded-box review

Date: 2026-09-09. Evidence: adversarial paper/code review and finite exact tests; **not a Lean proof**, not independent implementation verification, and not an arbitrary-N completion. Reviewed source `exact_box_v1.py` has SHA-256 `f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58`. Later changes require a new reconciliation entry.

The frozen baseline is `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`, SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The bounded-box proposal reviewed against the implementation is §3–5 of the post-freeze `AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`. New N=1 code does not edit or implement the original two-electron dictionary.

No invalid formula was found in the reviewed source. The following directional and normalization checks are material.

## Clipping restoration: the state must be the unclipped minimizer

On Ω=(-2R,2R)^3, with T=(1/2)∫|∇f|² and V_M=−Z min(1/r,M), Z≥1, one has q≤q_M and therefore λ≤λ_M. The uncut ground minimizer f exists by bounded-domain compactness and form coercivity; alternatively the argument works with normalized minimizing sequences. The pointwise clipping inequality and Hardy give

\[
0\le q_M[f]-q[f]\le\frac{2Z}{M}T[f].
\]

The previously derived bound q[f]≥T[f]/2−Z² implies T[f]≤2(λ+Z²). Thus, for any **clipped** upper bound U≥λ_M,

\[
\lambda_M\le q_M[f]\le\lambda+\frac{4Z(\lambda+Z^2)}M
\le\lambda+\frac{4Z(U+Z^2)}M.
\]

Consequently the code's restoration radius is correct, and only the lower endpoint needs restoration. Evaluating this argument solely at a clipped minimizer would not establish the displayed lower endpoint. The implementation's U is the minimum of three valid clipped upper bounds (16, a compressed-eigenvalue upper bound, and diagonal trial bounds), so it also bounds λ. The anchor orbital (1,1,1) is included for K≥1 and has clipped energy at most 3π²/(32R²)<1 for R≥1, independently of Z; the coarse 16 upper bound is valid.

## Complement and matrix bounds

An orbital outside the cube 1≤k_a≤K has kinetic energy at least π²((K+1)²+2)/(32R²). The lower rational π enclosure supplies a valid lower coefficient. The spin-up and spin-down copies have identical spectra and no cross terms; omitting their duplicate block preserves the actual N=1 spectral infimum.

For P onto the included orbitals and Q=I−P, kinetic cross terms vanish and ||V_M||≤B=MZ. The inequality 2B||u||||v||≤η||u||²+B²||v||²/η proves

\[
\lambda_M\ge\min\{\lambda_P-\eta,\Lambda-B-B^2/\eta\}.
\]

Replacing λ_P by its rational lower bound is conservative. The independently established hydrogenic square-completion lower bound −Z²/2 applies to q_M as well as q, so both lower-endpoint intersections in the code are valid. This lower bound is a paper continuum deduction; it is not a numerical reference-digit oracle.

On each cell, V_M∈[c−δ,c+δ]. Its constant contribution is c times the exact normalized overlap integral. The remainder is bounded by

\[
\left|\int_{\rm cell}(V_M-c)\phi_a\phi_b\right|
\le\frac\delta2\left(\int_{\rm cell}\phi_a^2+
\int_{\rm cell}\phi_b^2\right).
\]

The one-dimensional normalization is correct: x=4Ru−2R makes the product of two normalized sine functions times dx equal 2 sin(kπu)sin(lπu)du, whose cosine-difference primitive is the formula in the source. Tensor products therefore introduce no missing R or square-root factor. Interval diagonal masses are nonnegative upper bounds. The matrix intervals are symmetric; their midpoint-radius row-sum bound controls the Euclidean operator norm, hence the smallest eigenvalue perturbation.

Square-root bisection uses the exact integer square root of the scaled rational floor. Machin alternating series and the sine Taylor remainder are outward rational enclosures. Real sine argument reduction preserves signs and handles integer/half-integer arguments exactly. The Schur PSD decision handles negative diagonals and zero pivots; Gershgorin lower and minimum-diagonal upper brackets plus exact PSD decisions enclose the smallest eigenvalue.

## Parity/reflection optimization and total-schedule margin

Reflection in one Cartesian coordinate multiplies the orbital by (−1)^(k+1). Because the nuclear potential is even, opposite-parity products integrate to zero. For same-parity products, reflected cell integrals agree. The source correctly gives each reflection orbit multiplicity two per reflected noncentral coordinate and multiplicity one for the central cell of an odd grid. This retains the full finite orbital cube, not only even orbitals.

V_M has Lipschitz constant at most ZM². A cell has diameter 4√3 R/J<8R/J, so the exact midpoint potential radius is at most 4RZM²/J. For each fixed pair of orbitals, the sum of (W_aa+W_bb)/2 over the full grid is exactly one. Therefore the limiting cell-variation contribution to an entry radius is at most 4RZM²/J≤t/4 under the source schedule J≥16RZM²/t. As bits grows, all remaining interval errors on that fixed finite grid tend to zero, leaving a strict margin before the t threshold. K, J and every intermediate denominator may be very large, but are finite. This is a mathematical termination argument in the unbounded integer model, not a practical resource guarantee or a bit-cost bound.

At the accepted radius t=e/K³, row error≤e=ε/32. The conservative complement schedule makes its second branch at least 16, whereas the first is at most λ_P≤16. With eigenvalue bracket width ε/8, η=ε/8 and restoration≤ε/8, the returned width is at most

\[
\varepsilon/8+2(\varepsilon/32)+\varepsilon/8+\varepsilon/8
=7\varepsilon/16<\varepsilon.
\]

Independent finite checks are reproducible by

```sh
python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/computation/box/independent_review_checks_v1.py
```

The receipt `independent_review_checks_v1.json` records PASS for all 15,625 symmetric 3×3 matrices with the six independent entries in {−2,−1,0,1,2}, comparing the implementation to explicit nonnegativity of all seven principal minors. It also records 729 exact containment checks for the K=3 constant-potential matrix, including 98 offdiagonal positions with matching coordinate parities. Constant clipping uses R=1,M=1/4, since every radius in the cube is ≤√12<4. These tests target zero pivots, Schur signs, normalization and the reflection optimization; they do not prove general correctness.

The fresh-process checker rebuilds every matrix entry and scalar bound, which makes saved results replayable. It deliberately shares the same arithmetic implementation and therefore is not an independent verified checker kernel. Earlier development certificates with a different source hash correctly fail the current checker; preserving those certificates and creating new final ones is required, not overwriting historical evidence.
