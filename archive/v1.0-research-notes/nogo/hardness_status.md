> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Status of continuum hardness after the finite-basis counterexample

No literature search was performed for this assessment. It analyzes only the proved scope of the existing construction, elementary energy bounds, and the logical requirements of a reduction.

**Status: neither a constructive continuum-hardness reduction nor a general no-go theorem has been established.** The demonstrated failure of the particular Gaussian trial space is not a restriction on every possible nuclear configuration or every possible encoding. An elementary physical energy bound does not change that conclusion.

## What the completed example rules out

For the specified two-electron, two-nucleus instance, the certified projected energy exceeds 10^34, whereas the unrestricted continuum spectral infimum is at most zero. Therefore this prescribed trial space cannot approximate that continuum ground energy to small absolute error. The large kinetic-energy offset which is harmless for the finite-dimensional Hubbard comparison does not make these orbitals a continuum low-energy sector. The finite-dimensional Hamiltonian is nevertheless well defined and the small rescaled finite-dimensional operator error remains valid.

This excludes a proposed inference from this particular projected calculation to the physical spectral bottom. It does not prove that Coulomb systems of the same general form cannot encode a hard problem using entirely different low-energy states.

One two-site instance also cannot establish complexity hardness: hardness concerns a uniform polynomial-time transformation for arbitrarily large input instances, with controlled promises and errors. Conversely, failure of one instance or one family of trial spaces does not quantify over all such transformations.

## Why polynomial physical bounds do not preclude hardness

For illustration, an elementary bound sufficient here is

\[
-\frac{N}{2}\left(\sum_A Z_A\right)^2\le E_N\le0.
\]

The lower bound follows by discarding electron repulsion and applying the one-electron estimate to each electron. For a smooth one-electron function f and the bounded vector field

\[
F(r)=\sum_A Z_A\frac{r-R_A}{|r-R_A|},
\]

integration by parts gives

\[
\frac12\int|\nabla f+Ff|^2
=q_1[f]+\frac12\int|F|^2|f|^2.
\]

Since |F|≤Σ_A Z_A, the asserted lower bound follows by density and the Coulomb form estimates. The upper bound follows from electrons in mutually distant, increasingly broad packets, antisymmetrized; kinetic and pair-repulsion energies tend to zero and attraction is nonpositive. Neither inequality requires a normalized ground eigenvector.

If charges are bounded by a constant and N,M are polynomially bounded in the input size, this encloses E_N in a polynomial-width energy band. An inverse-polynomial promise gap fits inside that band. General finite-dimensional local-Hamiltonian promise problems likewise use polynomially bounded energy bands; an energy bound is not an algorithm for deciding on which side of a threshold a particular ground energy lies.

There is also no requirement that different input instances produce different ground energies. A decision reduction need only preserve YES and NO instances. Thus the polynomial number of separated energy bins in a bounded band gives no information-counting contradiction to hardness. Many inputs may map to the same energy or the same side of the promise gap. Polynomial-size descriptions of polynomially many nuclei on a polynomial grid can still form an exponentially large family of configurations; this observation merely removes a superficial counting objection and is not evidence that a reduction exists.

Bounds make thresholds outside the permitted physical band easy. They do not show that thresholds inside the band are easy. Specifically, an interval which the spectrum can never occupy is a **forbidden interval**, not a useful encoding window. A valid hard-instance construction would place its threshold pair inside an attainable energy range after a computable affine comparison shift. It would not request the continuum ground energy to equal the enormous positive energy of the demonstrated Gaussian projection.

## A precise target reduction statement

One possible target can be stated without assuming the missing construction exists. Fix a bound Z_max independent of instance size. Given a rational 2-local Hamiltonian input x of length L, with source matrix K_x of polynomial norm, thresholds a_x<b_x satisfying b_x−a_x≥1/q(L) for a fixed polynomial q, and the promise λ_min(K_x)≤a_x or λ_min(K_x)≥b_x, seek a polynomial-time map producing:

- N_x and M_x bounded by a polynomial p(L);
- integer charges 1≤Z_A≤Z_max;
- distinct nuclear positions on the explicitly specified grid p(L)^{-1}ℤ³ inside the cube [−p(L),p(L)]³;
- rational comparison data α_x>0, β_x, δ_x≥0 of polynomial bit length, with α_x and its reciprocal polynomially bounded;
- the full, nonmagnetic, fixed-nuclei Coulomb operator H_x, with no supplied trial-space restriction.

The desired energy and binding conclusions are

\[
\left|\inf\sigma(H_x)-\bigl(\alpha_x\lambda_{\min}(K_x)+\beta_x\bigr)\right|
\le\delta_x,
\]

\[
\alpha_x(b_x-a_x)-2\delta_x\ge\frac1{p(L)},
\qquad E_{N_x-1}(x)-E_{N_x}(x)\ge\frac1{p(L)}.
\]

The binding margin is an additional desirable requirement ensuring an isolated bound level; hardness of the spectral infimum alone does not logically require it. The grid convention above is a proposed precise restriction, not an interchangeable synonym for arbitrary rational coordinates of polynomial bit length.

If the stated map and inequalities were proved, choose output thresholds

\[
A_x=\alpha_x a_x+\beta_x+\delta_x,
\qquad B_x=\alpha_x b_x+\beta_x-\delta_x.
\]

YES inputs then satisfy E_N≤A_x; NO inputs satisfy E_N≥B_x; and B_x−A_x remains inverse-polynomial. This elementary last step is not the missing reduction. All the substantive work lies in constructing the physical instances and proving the uniform spectral estimate and promises.

## The missing quantitative lemma

A potential route would need a **nuclear-Coulomb low-energy simulation lemma**. No construction satisfying such a lemma is supplied here. In a proposed localized-electron route, the lemma would have to prove, uniformly in instance size, all of the following linked claims for an explicitly constructed family of bounded-charge nuclear layouts:

1. An identifiable localized orbital or cluster sector has the intended electron occupancy. Every unwanted charge distribution, extra low orbital, and competing spin or ionic configuration has a quantitatively controlled energy penalty.
2. Within that sector, exact Coulomb matrix elements and virtual transitions reproduce the requested Hubbard or spin couplings after a computable shift and scaling. Every long-range term, exchange term, induced many-body term, and approximation remainder is included in a norm or form estimate small relative to the promise gap.
3. The **full orthogonal complement** has a proved lower-energy bound. This must cover all continuum states outside the proposed localized sector, not just the next states in another finite basis. Coupling between the proposed sector and its complement must satisfy a bound strong enough to control the true spectral bottom.
4. Electron escape and ionization are controlled. If the stronger bound-state formulation is chosen, the construction must preserve an inverse-polynomial separation below the first ionization threshold.
5. Positions, charges, precision, number of particles, and the computation of all comparison constants obey the stated uniform polynomial bounds and grid restriction.

An operator-block formulation makes the third requirement concrete. Suppose P is a specified finite-rank orthogonal projection whose range lies in D(H), and Q=I−P. Establishing a lower bound q_H[v]≥Λ||v||² for all v in QH intersected with the form domain, and a suitable coupling estimate for QHP, together with an approximation for PHP, can support a spectral comparison. Merely displaying PHP, or finding a low eigenpair of PHP with a small residual, does not establish the needed lower bound on the complement or identify the lowest spectral branch. A candidate is not validated until these estimates are proved for its actual nuclear potentials.

The named lemma is a research obligation, not a claim that local wells formed by positive nuclei can realize the requested interactions. Bounded nuclear charges, geometric embedding, Coulomb tails, occupancy competition, and ionization may obstruct a proposed route. The present work establishes no theorem that these issues can be resolved simultaneously, and no theorem that they cannot.

## What would be required for a general no-go theorem

To rule out the target statement, one would need a result applying to **every** allowed encoding, rather than a defect of the present high-energy Gaussian family. Examples of logically adequate progress would be:

- an efficient algorithm for the entire promised bounded-charge/grid continuum family, together with the relevant complexity-class separation assumption if the conclusion is to exclude QMA-hardness;
- a universal structural restriction on spectra or interactions which is proved incompatible with every proposed reduction in a precisely delimited reduction model;
- a stronger mathematical obstruction to the target promises that actually quantifies over all allowed nuclear layouts.

A polynomial energy bound, a sufficient binding condition, or a failure of one basis does not supply any of these. An efficient algorithm for a special tractable subclass is useful but does not settle the full family's complexity. Nor would merely changing the proposed localization ansatz prove the opposite direction.

## Recommended next-session claim

Select the assessment category **neither constructive reduction nor general no-go established**. The defensible next step is a precisely delimited result: either prove the missing low-energy estimates for an explicit scalable family, or prove a narrow obstruction/tractability theorem under a transparent structural predicate. State exactly which family and which input, output, and precision model the theorem covers.

Do not present this status assessment as a new complexity theorem. The counterexample and elementary bounds identify obligations and invalidate a particular inference; they do not resolve continuum hardness. A newly exhibited sufficient tractable class also would not meet the original request for an exhaustive characterization of exactly all physically relevant classes.
