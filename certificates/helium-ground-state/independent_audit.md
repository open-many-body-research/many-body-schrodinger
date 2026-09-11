# Independent audit of the helium moment certificate

**Outcome:** no certificate-breaking discrepancy was found in the checked finite algebra or in the human derivation. This is an independent implementation and proof audit, **not a Lean proof** of the continuum identities. Only `independent_audit.py`, its log, and this report were written. No large trial integral was recomputed and no existing certificate was changed.

The executable audit is [independent_audit.py](independent_audit.py); [independent_audit.log](independent_audit.log) records Python version and SHA-256 hashes of the checked source files and saved certificates. The primary targets are `hylleraas.py`, `check_trial.py`, `THEORY.md`, and `helium_research/helium_method.md`. The subsequent source review also checked the rank-one spectral-projection proof in `helium_research/lower_bounds.md`.

## Independent moment derivations

Use perimetric variables

\[
r=y+z,\qquad s=x+z,\qquad u=x+y,\qquad x,y,z>0.
\]

Their Jacobian has absolute determinant 2 and r+s=x+y+2z. For nonnegative integers a,b,c, expand the three powers. Choosing powers yⁱ,xʲ,xᵏ in the respective factors leaves powers

\[
x^{j+k}y^{i+c-k}z^{a+b-i-j}.
\]

The resulting reference formula is a finite sum of positive rational terms, each equal to twice the binomial coefficients times

\[
\frac{(j+k)!}{\kappa^{j+k+1}}
\frac{(i+c-k)!}{\kappa^{i+c-k+1}}
\frac{(a+b-i-j)!}{(2\kappa)^{a+b-i-j+1}}.
\]

This independently checks the angular-polynomial recurrence used by the production code. **1,029 exact equalities passed:** indices a,b,c from 0 through 6 and κ in {1,2,7/3}.

For a=−1 and nonnegative b,c, insert the positive Laplace representation

\[
\frac1{y+z}=\int_0^\infty e^{-t(y+z)}\,dt.
\]

After the three positive coordinate integrations, the remaining factors are

\[
J_{mn}=\int_0^\infty(t+1)^{-m}(t+2)^{-n}\,dt.
\]

They satisfy J₁₁=log2, Jₘ₀=1/(m−1), J₀ₙ=2^(1−n)/(n−1), and Jₘₙ=Jₘ,ₙ₋₁−Jₘ₋₁,ₙ. Every boundary integral actually used is convergent. This differs from the production angular B recurrence. For c=−1 and nonnegative a,b, the further substitution x+y=w, x=wt cancels the reciprocal u against the Jacobian and reduces the calculation to integer beta and factorial integrals. **729 exact equalities passed:** the two radial orientations and pair inverse, indices through 8, at three values of κ.

The remaining cases a=c=−1 and a=b=−1 were checked against positive rational series enclosures. Here the coordinate reduction agrees with the human derivation, but the constant evaluation does not use its logarithmic or reciprocal-square closed forms:

\[
B(n,c)=\sum_{\ell\ge0}
\frac1{(n+2\ell+1)(n+2\ell+c+2)}.
\]

For a cutoff K, the omitted sum is at most

\[
\frac1{(n+2K+1)^2}+\frac1{2(n+2K+1)}.
\]

This follows by bounding with a decreasing inverse square and applying the integral test. **54 double-negative checks passed** with K=1024. These enclosures are intentionally much wider than 512-bit intervals; they detect errors in signs, factors, and branches without pretending to independently reproduce 512-bit accuracy. The excluded triple (−1,−1,−1) has a divergent radial integral and is correctly rejected by the production precondition.

## Hamiltonian, measure, and operator domain

A separate Cartesian automatic differentiation implementation stores the value, six first derivatives and the Cartesian Laplacian of each expression. It differentiates the three distances directly, using rational Cartesian points whose distances are rational. It does not use the production mixed-coefficient formula. **1,500 exact pointwise Hamiltonian identities passed** for monomials with exponents through four, four geometries, and three parameter pairs. The exponential is removed algebraically before comparison, so no approximate exponential enters these tests.

An additional reference calculates the kinetic bilinear form from gradients and integrates it with the independent perimetric moments. **108 exact energy-form checks passed.** This tests both the mixed-derivative coefficient and the integration-by-parts relation, rather than only symmetry of the assembled matrix. Three product-orbital normalization checks also passed:

\[
I(1,1,1;2\alpha)=\frac1{8\alpha^6},
\qquad
\|e^{-\alpha(r+s)}\|_{L^2(\mathbb R^6)}^2=\frac{\pi^2}{\alpha^6}.
\]

Thus the common angular factor 8π², the measure rsu dr ds du, and the normalization cancellation are consistent.

The operator-domain justification in the human derivation is valid for these **nonnegative-power polynomial** trials. More explicitly, with t=r+s, classical second derivatives off the collisions satisfy a bound of the form

\[
|D^2(e^{-\alpha t}P)|
\le C e^{-\alpha t}(1+t)^d
       (1+r^{-1}+s^{-1}+u^{-1})
\]

for some finite C,d. First derivatives of distances are bounded; each distance Hessian contributes only a single inverse distance. Each inverse distance is locally square integrable in its three normal dimensions. Exponential decay controls the exterior. Removing tubes around the collision sets in integration by parts gives vanishing boundary contributions, since first derivatives are locally bounded and tube-boundary measure shrinks quadratically in the normal radius. Therefore the displayed derivatives are weak derivatives and the trial lies in H²(ℝ⁶). This argument must not be transferred to arbitrary Laurent-polynomial trial functions: the Laurent terms here describe the Hamiltonian action, while the original P has nonnegative exponents.

## Constants, variance, and Temple step

The `log2_bounds` remainder agrees with a geometric majorant of the positive atanh series. Its numerical enclosures were independently checked inside alternating-harmonic enclosures. Twenty directed-decimal checks passed, including small negative values where truncation toward zero would be unsound.

The norm and first Hamiltonian moment are rational. The squared-action moment lies in ℚ+ℚ log2+ℚ π²; the π² branch is required. The variance is H₂/S−a², with a=H₁/S, and the outward arithmetic respects coefficient signs. Clipping only the variance lower endpoint at zero is justified by its squared-norm interpretation. The Temple lower bound uses the unaltered upper endpoint. Saved certificate final arithmetic was replayed exactly, including the transitions from stored moments to variance, the separator denominator, the lower endpoint and decimal rounding. These checks establish consistency of the stored data with that arithmetic; they do not replace recomputation of the stored continuum moments.

The spectral separator β=−5/2 is correctly a full fermionic continuum statement. The charge-two one-electron hydrogenic spectrum has energies −2 for 1s and −1/2 for the next principal level. Exactly two spin orbitals occupy 1s, so the lowest two-electron determinant is unique at −4, and the next fermionic min-max level is −5/2. The one-electron continuum begins at zero. Positive electron repulsion preserves the lower bound on the second min-max level. A trial mean a<β therefore isolates the unique ground eigenvalue below β; no experimentally estimated excited energy is needed. Integrating the nonnegative polynomial (λ−E₀)(λ−β) against the trial scalar spectral measure gives

\[
\operatorname{Var}(H)+(a-E_0)(a-\beta)\ge0,
\]

which yields the implemented lower bound. This uses a finite second spectral moment, guaranteed by membership in D(H); it does not apply the operator twice or require membership in D(H²). The explicit rank-one spectral-projection argument in `lower_bounds.md` also establishes discreteness and uniqueness below the separator without invoking compact resolvent or an unproved excited-state estimate. The hydrogenic spectral theorem, comparison, self-adjointness, and spectral-measure step remain paper/theorem-library dependencies until formalized.

## Input schema and provenance

All numerical audit comparisons affecting PASS use exact integers/Fractions or outward intervals. Deliberately invalid float and boolean inputs appear only in rejection tests. The current checker accepts rational strings or integers for mathematical scalar fields, rejects floats and booleans there, and rejects JSON floating-point tokens. Nonfinite JSON constants are additionally tested for rejection in mathematical scalar fields. Trial indices and coefficient counts are independently checked without constructing a moment matrix.

The two minor issues identified during the first audit are resolved: `THEORY.md` now exists, and exact input-type validation is explicit. New certificates record the supplied trial SHA-256 and exclude timing metadata; wall-clock timing is confined to the execution log. The audit verifies each saved hash against the referenced trial file and uses each certificate interval_bits value, including higher-precision runs. Older certificates without a trial hash are still checked arithmetically and are explicitly labeled LEGACY; they are not silently credited with the new provenance guarantee. Final order-20 or higher certificates must satisfy the new schema.

No mathematical correction to the moment or Temple formulas is proposed by this audit. The evolving saved-certificate inventory and actual executed coverage are recorded in the final PASS log rather than hard-coded into the test script.

The final execution on 2026-09-09 passed all retained independent algebra tests and replayed all seven saved certificates: five explicitly labeled legacy certificates and the two final order-20 certificates at 512 and 768 bits. Both final files verified the SHA-256 of the same 946-function rational trial and reproduced the outward interval [−2.903725202862, −2.903724370072] hartree, of exact width 0.000000832790 hartree. The audit checked the precision-specific variance enclosures, every subsequent rational Temple operation, and all stored trial schemas without rebuilding either large moment matrix. Source and certificate hashes are recorded in the successful log.
