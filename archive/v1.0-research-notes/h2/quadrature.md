> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Rational Coulomb quadrature certificate

Status: **PROVEN (human mathematical derivation only)** for the analytic identities and remainder bounds below, with executable rational interval checks. This is not a Lean formalization. The implementation is [gaussian_integrals.py](h2/gaussian_integrals.py); the Gaussian conventions and independent integral derivations are in [moment_audit.md](h2/moment_audit.md).

## Scope and public interface

The input consists of exact rational numbers a,b,c,m,n with a,b>0 and c²≤ab. The jointly Gaussian three-vectors Y,W have covariance matrices aI₃/2,bI₃/2 and cross covariance cI₃/2, with axial means m e_z,n e_z. The output encloses E[1/(|Y||W|)]. Every physical-space integral extends over the original unbounded Gaussian configuration space.

`single_inverse(a,m)` encloses E[1/|Y|]. `boys_moments(T,max_k)` returns enclosures of F₀(T),…,F_max_k(T), where F_j(T)=∫₀¹u²ʲexp(−Tu²)du. `inverse_product(a,b,c,m,n,abs_tol=...,bits=...,max_cells=...)` returns an interval; the actual width, rather than the requested tolerance, is authoritative. `LAST` records the method, cell count, analytic error and whether the requested width was reached. `STATS` contains cumulative counters.

## Early bound for negligible primitive pairs

The inverse-square identity below gives E|Y|⁻²=(2/a)∫₀¹exp[−(m²/a)(1−z²)]dz≤2/a and similarly E|W|⁻²≤2/b. These finite bounds establish the integrability needed for Cauchy–Schwarz, which yields

    0 ≤ E[1/(|Y||W|)] ≤ √(E|Y|⁻² E|W|⁻²) ≤ 2/√(ab).

The bound is valid for all admitted correlations and means. The engine first encloses 2/√(ab), rounds that enclosure to the output precision, and checks whether its upper endpoint is at most `abs_tol`. If so it returns the interval from zero to that endpoint, with zero quadrature cells and the `coarse_cauchy_schwarz` counter incremented. This returns an absolute enclosure, not an estimate based on primitive coefficient cancellation. Allocation of the tolerance to a weighted matrix contribution remains the calling certificate's responsibility. The centered proportional case attains the bound and supplies an exact test; a tighter requested tolerance bypasses the shortcut.

Every subsequent result is also intersected with this universal interval before return. Intersection of two enclosures of the same exact expectation preserves validity. Thus an insufficient quadrature cell budget cannot return a needlessly large upper endpoint. An empty intersection raises an error; it is not silently accepted. The final interval width determines whether the tolerance was met.

## Exact elimination of one integration variable

For c²<ab put r=c²/(ab), T=m²/a, U=n²/b, C=cmn/(ab). The Gaussian Laplace calculation gives the expectation as 4/(π√ab) times the integral of

    f(u,z) = D(u,z)^(-3/2) exp(−N(u,z)/D(u,z)),
    D = 1−r u²z²,       N = T u²+U z²−2C u²z²,

over the unit square. Here D>0 and N≥0. For fixed z let L=1−r z² and B=(m−(cn/b)z²)²/a. Direct algebra gives

    N/D = U z² + B u²/(1−r z²u²).

The substitution v=u/√(1−r z²u²) has derivative D^(-3/2) and upper endpoint 1/√L. Therefore the exact inner integral is

    g(z) = exp(−U z²) F₀(B/L)/√L.

The primary implementation applies a one-dimensional Gauss rule to g. The original tensor rule for f remains available for an independent comparison. Interchanging a,m with b,n leaves the expectation invariant; the code uses whichever orientation has the smaller proved derivative bound.

### Positive Boys integral at large arguments

Only inside the reduced integrand, `_line_boys_f0` uses the following bound when the entire argument interval lies in [128,∞):

    sqrt(π)/(2sqrt(t)) − exp(−t)/(2t) ≤ F₀(t) ≤ sqrt(π)/(2sqrt(t)).

Indeed, the substitution s=sqrt(t)u in the Gaussian integral shows that the difference between the upper expression and F₀(t) is t^(-1/2)∫_{sqrt(t)}^∞exp(−s²)ds. In that positive integral, 1≤s/sqrt(t); integrating s exp(−s²) gives the stated upper bound exp(−t)/(2t). This proves the enclosure for every t>0, independently of the threshold choice. For an interval [l,h], the implementation encloses the central expression by rational interval operations and subtracts the upper enclosure of exp(−l)/(2l), because this tail bound decreases for positive l. It retains the complete resulting width, including outward rounding. The threshold 128 is a performance choice, not an assumption of zero tail or guaranteed precision. Arguments crossing the threshold use the existing Boys routine. In particular, the separate `erfc` subtraction in the prolate integrand remains unchanged, since a small absolute Boys error there need not give a small relative erfc error.

## Effective derivative bound

Take a real box [x₀,x₁]×[y₀,y₁]⊂[0,1]². Write d_min=1−r x₁²y₁² and d_max=1−r x₀²y₀². Since N is bilinear in x²,y², its extrema are attained at the four corners. Let N_max be its maximum and E_min=max(0,N_min/d_max). Then N/D≥E_min throughout the real box.

To differentiate in x, hold y real and allow a complex perturbation h with |h|≤R. Set

    p = R(2x₁+R),
    d_pert = r y₁² p,
    n_pert = (T+2|C|y₁²)p,
    q = d_min−d_pert.

Accept the radius only when q>0. The perturbed denominator lies in the right half-plane, so the inverse power has one analytic branch, and its magnitude is bounded below by q. Subtracting the real quotient N/D from its perturbed value gives

    |E_complex−E_real| ≤ W
        := n_pert/q + N_max d_pert/(q d_min).

Consequently |f_complex|≤q^(-3/2)exp(W−E_min). Here 0<q≤1, so a rational upper bound is

    M = q^(-2) 3^ceil(max(0,W−E_min)).

This uses e<3, which follows from the exponential series and a geometric bound on its tail. Cauchy's integral formula now yields |∂ₓ¹⁶f|≤16! M/R¹⁶. The y bound follows by interchanging variables. The implementation takes the smallest valid bound from finitely many rational radii. If these candidates fail, it sets δ=d_min, K=1+N_max+T+U+2|C| and R=δ²/(64K), with T interpreted in the chosen differentiation direction. Since δ≤1 and K≥1,

    p ≤ 3R = 3δ²/(64K),
    d_pert ≤ 3δ²/(64K),       q ≥ 61δ/64,
    n_pert/q ≤ 3δ/61 ≤ 3/61,
    N_max d_pert/(qδ) ≤ 3/61.

Therefore W≤6/61<1 and the integer exponent in M is at most one. This avoids constructing an astronomically large integer near perfect covariance correlation. The resulting radius can still give a very conservative derivative bound, which the resource-cap and universal-intersection logic report honestly. No floating-point minimization chooses or validates a radius.

For g(z)=∫₀¹ f(u,z)du, use the bound on the box [0,1]×[z₀,z₁]. Differentiation under the integral is valid because the same positive complex denominator bound holds uniformly in u. Thus |g⁽¹⁶⁾|≤16! M/R¹⁶. This preserves the two-variable analytic control after the exact reduction.

## Gauss rule and remainder

The eight nodes are the roots of

    P₈(x)=(6435x⁸−12012x⁶+6930x⁴−1260x²+35)/128.

Four rational positive brackets and their negatives have sign changes and are disjoint. They therefore contain all eight roots, each simple. Exact rational bisection encloses each node. The associated positive weights are 2/[(1−x²)P₈′(x)²], evaluated outward.

The usual Gauss identity follows from Legendre orthogonality: divide a polynomial of degree at most 15 by P₈ and integrate its P₈ multiple using orthogonality; the remainder has degree at most 7 and is integrated by its Lagrange interpolant. Integrating the Lagrange polynomials gives the stated weights. Hence the rule integrates degree 15 exactly and its weights sum to the interval length.

For a C¹⁶ real function, its degree-15 Hermite interpolant agrees with the function and first derivative at all nodes. The interpolation remainder is bounded by sup|g⁽¹⁶⁾|/16! times the square of the monic node polynomial. Orthogonality gives ∫₋₁¹P₈²=2/17 and the leading coefficient (16)!/[2⁸(8!)²]. Scaling to a cell of length ℓ gives

    |integral_cell g−Q_cell g|
      ≤ ℓ¹⁷ (8!)⁴ / [17(16!)³] sup|g⁽¹⁶⁾|
      ≤ ℓ¹⁷ (8!)⁴ / [17(16!)²] M/R¹⁶.

This is exactly the rational error used by `_line_error`. The adaptive partition sums these bounds over all leaves. The interval evaluation at enclosed algebraic nodes accounts separately for node, weight and special-function uncertainty. Multiplication by an outward enclosure of 4/(π√ab) also includes normalization uncertainty. If the cell cap is reached, the still-valid accumulated error is retained.

## Proportional forms and the singular corner

When c²=ab, set k=c/a. The second form is k times the first random form with an adjusted center, contributing the factor 1/|k|. The reduced prolate integral uses

    d=|m−n/k|/2,       z=(m+n/k)/2.

Its integrand and rational derivative recurrence are proved in `moment_audit.md`. For degree-15 midpoint Taylor quadrature on K equal cells, the exact remainder bound is

    2 M₁₆ / [a·17!·K¹⁶],

before the factor 1/|k|. Only rational midpoints occur. The code chooses K using this explicit bound. The prolate formula extends to d=0 by the independently derived inverse-square identity; at zero displacement the answer is exactly 2/(a|k|). Thus no r=1 value is inserted into a smoothness argument that requires r<1.

The erfc evaluation uses erfc(x)=1−2xF₀(x²)/√π. Extra precision is allocated before multiplication by a positive exponential, and all interval error is retained. Proven ranges erfc∈[0,2] and nonnegativity of the desired expectations permit interval intersections with those ranges.

## Arithmetic and measured validation

The canonical interval module is `certified_interval`, loaded from the existing `gaussian` directory. Its endpoints are dyadic rationals. Integer division, exact fractions and integer square roots control rounding; π, exponentials and Boys functions use explicit analytic series/tail bounds. Python float inputs are rejected. Timing and displayed decimal widths in the benchmark are empirical fields and play no role in any enclosure.

[gaussian_integrals_test.log](h2/gaussian_integrals_test.log) records tests against centered exact values, a symmetric prolate closed form, the retained tensor formula, exchange symmetry and a deliberately insufficient resource cap. [gaussian_integrals_benchmark.json](h2/gaussian_integrals_benchmark.json) records 64 kernels from 16 rational H₂ trial parameters: every returned interval had width at most 10⁻¹⁰. The measured run took about 6.81 seconds. This finite benchmark is **EMPIRICAL** performance evidence, not a complexity theorem or a complete molecular residual certificate.
