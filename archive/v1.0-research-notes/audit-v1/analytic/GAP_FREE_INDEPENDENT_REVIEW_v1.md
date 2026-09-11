> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the gap-free continuum reduction

Date: 2026-09-09. Status: bounded independent paper review; no solver execution, Lean proof, or status upgrade by consensus.

Reviewed in full: `../arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`, SHA-256 `bf82d2a4d6c8cf8452a7e926e5ad55cdc4c17cd7533efa8b0591f6f14ef0192b`. The accompanying `ARBITRARY_N_SCOPE_v1.md` was also read in full. Their frozen baseline is `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`, recorded SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. This review concerns the new construction, not the unreviewed sections of that frozen baseline.

No substantive mathematical defect was found in the displayed localization, clipping, complement or quadrature estimates. The following independent calculations explain that assessment and its limits.

## 1. Domain, fermionic localization and recursion

The pair Hardy estimate has the correct factor two after the orthogonal relative-coordinate change. Summing its square-root bounds over the `N(N−1)/2` pairs gives `sqrt(N)(N−1)||grad psi||`; adding the nuclear bound gives equation (2). The completion-of-squares identity (3) has Coulomb coefficient `−2 alpha`, since the divergence of `x/|x|` is `2/|x|`. Its two choices of alpha yield both lower bounds (4) and (5).

The monotonicity `E_N<=E_(N−1)` is formulated at the form infimum rather than assuming a bound eigenstate. A compact-support approximation of the interior state and a distant, dilated extra bump have disjoint one-particle supports. Antisymmetrization therefore preserves the stated internal expectation after normalization; cross terms vanish by those supports and new interactions tend to zero. This works for a correlated interior state and includes spin.

Each max-norm cutoff is Lipschitz and its gradient has norm at most `pi/(2R)` almost everywhere. Product differentiation and `chi_i²+eta_i²=1` give equation (7) without an extra factor `2^N`. The fully interior product is permutation symmetric and has zero trace on the Dirichlet box. A mixed product preserves only the permutation subgroup of the interior labels; the construction correctly uses this subgroup when slicing, rather than incorrectly claiming that every localized state lies in the full fermionic subspace. Dropping exterior repulsions and kinetic terms yields equation (9), and monotonicity makes its replacement by `E_(N−1)−NZ/R` legitimate even for the empty interior cluster.

The coefficient of the IMS error is one half of (7), giving `N pi²/(8R²)`. The rational replacement in (11) is an outward enlargement using `pi²<10`. Its interval width bound follows from the max-norm Lipschitz estimate for min. No essential-spectrum threshold is substituted for an excited-level separator.

## 2. Clipping and a common anchor

The maximum of `r−Mr²` is `1/(4M)`, which gives (12). The nuclear clipping error is at most `(Z/M)||grad psi||²=(2Z/M)T`; the pair sum is at most `((N−1)/(2M))||grad psi||²=((N−1)/M)T`. Thus the absolute form error in (13) correctly includes the opposite signs of the two clipping changes.

Both forms obey `(1/2)T−NZ²`, because the clipped attraction is weaker and either repulsion is nonnegative. The stated spin-up sine Slater determinant is admissible for every positive integer N. Its kinetic bound is deliberately generous. Pair Cauchy–Schwarz gives `(N−1)sqrt(2NT)<=T+N(N−1)²/2`, so the shared upper bound U controls both true and clipped minima. Compactness of the Dirichlet form embedding and (5) supply actual minimizing vectors with `T<=2(U+NZ²)`. Applying the absolute clipping error to each minimizer proves the two-sided estimate (15). No false monotonicity of the total clipped energy is needed.

## 3. Omitted continuum subspace

The full finite Slater space includes all determinants whose spin orbitals have three sine indices at most K. Since the complete Dirichlet kinetic basis is being used, every omitted determinant has an index at least K+1 and kinetic energy at least the displayed Lambda. The presence of the full spin basis is important; a selected spin ansatz would not suffice for the asserted fermionic ground energy.

The potential bound B controls the off-diagonal P/Q term. The inequality

\[
2B\|P\psi\|\|Q\psi\|
\le\eta\|P\psi\|^2+(B^2/\eta)\|Q\psi\|^2
\]

gives (19), with both signs and the placement of eta correct. Since the finite space contains the anchor, `lambda_P<=U`; the kinetic cutoff test (20) then proves `lambda_P−eta<=lambda_M<=lambda_P`. This is a quantitative continuum lower bound and not merely a Ritz upper bound.

## 4. Entry evaluation and rational eigenvalue bracketing

For fixed spin assignment, a normalized determinant product has magnitude at most `N!(2R)^(−3N)`. Differentiation in one Cartesian coordinate acts on one row of each determinant and costs at most `pi K/(4R)` per determinant. Their product derivative is therefore bounded by `C0 pi K/(2R)`. Each affected clipped pair contributes at most M² to the coordinate Lipschitz constant; the nuclear term contributes ZM². Product differentiation gives exactly (22).

Every point of a midpoint cell differs from the midpoint by at most `2R/J` in each of `3N` coordinates. Multiplying the coordinate Lipschitz bound by cell volume, summing cells, and summing all spin assignments gives (23). The modulus is explicit and computable, although extremely expensive.

At rational grid points, the clipping branch can be chosen by an exact comparison of a rational squared distance with `M^(−2)`. It is unnecessary to decide equality of a transcendental value. In the other branch the square root is positive, so ordinary interval refinement computes it. Rational series for pi and sine and finite determinant sums provide effective point evaluation. The real symmetric matrix error bounded entrywise by `e/m` has operator norm at most e.

The starting bracket `[−B−1,U+1]` contains the lowest eigenvalue of the rational approximate matrix: kinetic energy is nonnegative, the true compression is bounded below by `−B`, its upper bound is U, and the matrix perturbation e is less than one. Exact PSD decisions can bisect this eigenvalue without a real-number sign oracle. The returned interval width sums to `9 epsilon/16`, as written.

For the eventual implementation, make two edge cases explicit: `BoxEnclose` is only needed for N>=1, because `AtomicEnclose` handles N=0; otherwise require positive M and K separately in the exposed box contract. The PSD routine should explicitly reject a negative diagonal before its zero-diagonal and positive-pivot cases. These are minor specification details, not failures of the displayed atomic reduction.

## 5. Termination and limits

The recursive call at precision `p+3` returns width at most `2^(−p−3)=epsilon`; the box routine is requested at the same epsilon. The chosen R makes both localization error terms at most epsilon, so the parent width is at most `3 epsilon<2^(−p)`. Recursion decreases N. The finite cutoff and quadrature searches have explicitly increasing parameters with known error bounds. This verifies the mathematical reduction conditional on a total correct realization of the specified box routine.

The construction is useful even if the N-electron energy is not attained. Its independence of RWA, a ground-state gap, and unknown decay constants is supported by the proof. This review does not provide a built `BoxEnclose`, formalize real analysis or machine arithmetic, run a new energy calculation, or prove a complete bit-operation count. It supplies no polynomial precision bound: already the chosen R and M grow exponentially in p, and the dimension and quadrature grow accordingly. No novelty claim is inferred.
