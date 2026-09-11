> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Candidate D: explicit conforming hp definitions and pilot evidence

All energy and residual numbers in this directory are **EMPIRICAL**. No hp
energy interval has been certified here. The finite rational shape audit is
separate from the floating-point quadrature studies.

## Principal full tensor dictionary

Use the report's half-perimetric variables a,b,c and N>=1. The raw screening
files use n=N-1. Put

* p_N = 3 + floor((N-1)/3)^2;
* breakpoints B_N = {0, 2^(1-N), 2^(2-N), ..., 2^N};
* outer endpoint T_N=2^N;
* S_N = all C1 functions on [0,T_N] which are polynomials of degree <=p_N
  on each breakpoint interval and have value and derivative zero at T_N.

Extend every S_N function by zero beyond T_N. No value or derivative condition
is imposed at zero. Generate the basis by ordinary clamped B-splines: endpoint
knots have multiplicity p_N+1, interior knots multiplicity p_N-1. Remove the
last two B-splines. Every knot and piecewise-polynomial coefficient is rational.

The full dictionary is the exchange-symmetric part of S_N tensor S_N tensor
S_N: B_i(a)B_i(b)B_k(c) and
[B_i(a)B_j(b)+B_j(a)B_i(b)]B_k(c), i<j. Multiply its spatial members by the
unit singlet spinor. These are independent: tensor-product independence first
gives independence before symmetrization, and the displayed symmetrized
supports in that tensor-product index set are disjoint. Thus the reported
dimensions are actual dimensions, not numerical ranks alone.

There are 2N cells in one variable, d_N=2N(p_N-1) one-dimensional basis
functions, and m_N=d_N^2(d_N+1)/2=O(N^9) symmetric tensor functions. N=1,2,3
give m=40,288,936. All three pilot levels still have p=3; they primarily test
geometric h refinement and tail extension. They cannot identify an asymptotic
hp exponent.

**PROVEN (existing paper), instantiated here:** these functions lift to D(H)
by the finite-hp membership argument in TWO_ELECTRON_THEOREM.md Section 4.
They are globally C1, have bounded piecewise second derivatives, and match
zero with first derivatives at their outer boundaries. Exchange symmetrization
preserves this property. No artificial condition is imposed on collinear
faces or collision axes.

**PROVEN (this session), elementary finite construction:** the spaces are
nested. The new mesh retains every old knot, the degree never decreases, and
an old function extended by zero has C1 matching at the old outer endpoint.
The B-spline recurrence is a deterministic rational generator. A coarse common
denominator is the p_N-th power of the product of all nonzero differences of
distinct knots; there are O(N^2) such differences, each of O(N) bits. This
gives a polynomial bound (coarsely O(N^5), with harmless polynomial padding)
on local coefficient bit heights. Local coordinates and endpoint powers also
have polynomial bit heights. This is a parameter-size argument, not RATE.

## Finite moments and the explicit certificate path

Omit the common positive factor 16*pi^2. Set w=(a+b)(a+c)(b+c). For rational
piecewise polynomials, G_ij=int w F_i F_j and
A_ij=(1/2)int w grad(F_i)^T Gmetric grad(F_j)+int w V F_i F_j are rational,
because w, wGmetric and wV are polynomials. These forms are the continuum
forms; Q is not the square of a projected Hamiltonian.

Write P_i = -(1/2)div(wGmetric grad(F_i))+w V F_i, a polynomial on each cell.
Then Q_ij=int P_i P_j / w. This is a fixed-dimensional rational integral with
integrable boundary singularities. A particular elementary interval algorithm
is available:

1. On the origin cube, use six coordinate orderings and the rational Duffy map
   a=h*rho, b=h*rho*t, c=h*rho*t*v (and permutations). Jacobian/w is
   1/[rho(1+t)(1+v)(1+tv)]. Each P_i has total order at least two at the
   vertex, so P_i P_j cancels the radial singularity.
2. A cell touching exactly one pair-collision axis has two coordinates starting
   at zero. Split their square into its two orderings and substitute
   a=h*rho,b=h*rho*t. Its Jacobian cancels the vanishing factor a+b. All
   remaining denominator factors stay positive.
3. Each positive remaining denominator has an explicit rational lower and
   upper bound with upper/lower <=3, using the dyadic mesh. Expand its inverse
   about its rational midpoint. If D/Dmid=1-z, then |z|<=1/2; the K-term
   series remainder is <=2*2^(-K)/Dmid. Origin factors have the smaller
   ratio 1/3. Polynomial coefficient absolute sums bound numerators.
4. Multiply the finite polynomial sums and integrate monomials exactly. Bound
   all product-remainder terms using their rational envelopes. The output is
   a rational interval; it need not be expressed in a fixed log/pi field.

This is a concrete route to polynomial precision cost: p_N and the polynomial
degrees, cell count, coefficient heights, reciprocal midpoint heights and
logarithms of numerator envelopes are polynomial in N. Taking
K=s+poly(N) gives entry error <=2^-s; dense three-variable polynomial
arithmetic and exact monomial integration take polynomially many operations
on polynomial-bit integers. No infinite-dimensional analytic regularity is
used in this finite-moment argument. A production interval implementation
and its independent audit have NOT been executed in this pilot.

An independent rational Gram matrix with polynomial entry height then gives
lambda_min >=2^-poly(N) by denominator clearing and an integer determinant
bound. Consequently coefficient height has a concrete proof path here rather
than relying on the observed condition numbers. An implementation must still
record its chosen scaling and regularization in the certified optimization.

## Continuum-action implementation and checks

screen_tensor_hp.py evaluates the exact differential expression from Section 4
on each polynomial cell, with first-order drift
(-1/r+1/s+2/u, 1/r-1/s+2/u, 1/r+1/s-2/u). It integrates F_i F_j,
F_i H F_j and (H F_i)(H F_j) independently, including Duffy treatment of
origin and axis cells. It selects by maximizing G/(Q+10A+25G+tau I),
sigma=-5 and tau=2^-80, after exact power-of-two basis scaling.
The code's tau is measured in the reduced weighted inner product with the
common 16*pi^2 omitted. On the raw physical polynomial basis this corresponds
to the positive parameter tau_phys=16*pi^2*2^-80. All unregularized shifted
quotients, means, variances and residuals are unchanged by this convention;
the printed tau must not be misidentified as a dyadic raw-physical penalty.

The eigenproblem and quadrature in the screening code are floating-point.
There is an eigen residual diagnostic but no certified additive-optimization
bound. This limitation is explicit in every raw result. The phase-1 candidates
are rationalized and independently reevaluated by check_tensor_mp.py using
mpmath with no NumPy arithmetic. Neither calculation is an interval certificate.

audit_finite_shapes.py uses only Fraction. It checks the exact C1 equalities
at all knots for the three pilot dictionaries and checks the perimetric action
against the independent r,s,u action on rational monomials and rational points.
The finite checks supplement the displayed algebraic proof; they are not a
proof of RATE.

The full tensor N=2 rational witness was recomputed at 50 decimal digits with
12-point Duffy/Gauss rules and at 60 digits with 20-point rules. Its shifted
objective changed by approximately 9.5e-16 between those two quadrature rules;
the 60-digit value is 4.5453016999883928000470934043. The N=3 witness was
recomputed at 60 digits with 12-point rules, obtaining shifted objective
4.4670073312241530578800432419 and residual approximately
0.24853695653434789533. Float64 20-to-28-point recomputation changes that
residual by about 4e-12. These are sensitivity checks, not rigorous remainders.

## Separate radial-shell hp prototype

This is a second, explicitly labeled geometric hp variant, not a subspace of
the principal axis-aligned tensor mesh. Set t=a+b+c, d=a-b. For n>=1 use
radial knots {0,2^-n,...,2^(n+2)}, radial polynomial degree n+3, C1 matching,
and zero value/derivative at the outer endpoint. Multiply each retained radial
B-spline S(t) by c^j d^(2k), j+2k<=n. All members are compactly supported
piecewise polynomials on simplex shells and satisfy the same existing D(H)
lemma. The spaces are nested and have dimension O(n^4); the six pilot sizes
are 30,112,270,594,1092,1920.

This shell geometry resolves the triple vertex directly. It does not supply
the full tensor family's explicit refinement along each collision axis, so
its numerical slope must not be attributed to the principal dictionary.
Its true-action moments separate into exact polynomial radial integrals and
two-dimensional angular rational integrals. The scalar moment checks use
high-precision Gauss quadrature; the absence of a rigorous quadrature remainder
is why they remain EMPIRICAL.

The initial screen whitened G. To control the high-energy numerical spectrum,
the implementation was changed to maximize G/(D+tau I), mathematically the
same regularized fixed-shift objective. The exact initial source is preserved
as screen_hp_initial_91f6ca91.py, with the SHA recorded by its original outputs.
Preferred repeat rows n=1,...,5 are in inverse_selection/; n=6's original row
already used the inverse formulation. No global Rayleigh-variance optimizer
has been used.

The n=6 rational shell witness gives shifted objective
4.3944371748046179297717957763 and residual
0.0072885471995298824188148860 at 70 decimal digits with a 48-point angular
rule. Its 60-digit/32-point rerun agrees in the shifted objective through
approximately 38 decimal places. This precision is an empirical quadrature
stability result, not certified accuracy and not additional helium digits.

## Interpretation

**EMPIRICAL:** full tensor pilot condition numbers after rational power-of-two
scaling are roughly 3.8e3,7.7e3,8.6e3; the shell prototype grows from 1.6e3
to 2.9e12. Full tensor residuals fall from about 1.61 to 0.343 to 0.249.
The shell prototype's six residuals fall approximately 1.68,0.739,0.267,
0.0867,0.0259,0.00729, but at substantially larger dimensions than compact
global Hylleraas/Fock bases.

**OPEN:** graph RATE for either hp family. No slope in this pilot proves it.
For the principal tensor dictionary, the highest-leverage analytic break
remains LPWA followed by interpolation/gluing in the physical weighted graph
norm and the exterior/tail construction. Its finite-domain conformity,
rational generator, polynomial dimension and concrete reciprocal-series
moment route support a proof effort even if another dictionary wins the
small-dimension numerical comparison. A recommendation must still weigh the
other candidates' measured evidence; this note does not declare a winner.
