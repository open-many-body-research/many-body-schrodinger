> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exact Hylleraas moments and a continuum Temple certificate for helium

Status: **PROVEN (human derivation only)** for the identities and conditional certificate below. No numerical energy or successful one-microhartree certificate is asserted by this document. Exploratory optimization may use floating point; the final trial parameters, moments, and enclosing endpoints must be re-evaluated exactly or with outward rational bounds. No new literature search was used for this derivation.

## 1. Physical problem and trial states

Use the helium electronic Hamiltonian in Hartree atomic units,

    H = −(Δx+Δy)/2 − 2/|x| − 2/|y| + 1/|x−y|,

on the full antisymmetric two-electron spin space. There is one nucleus of charge `Z=2` at the origin and no nuclear-repulsion constant. Let

    r=|x|, s=|y|, u=|x−y|,
    Phi(x,y)=exp[−alpha(r+s)] P(r,s,u),

where `alpha>0` is rational, `P` has rational coefficients, and `P(r,s,u)=P(s,r,u)`. Multiplying the spatial function by the normalized antisymmetric spin singlet produces a fermionic trial state. Normalize only after constructing the exact squared norm. Polynomial times exponential trial functions of this form belong to the Coulomb operator domain `H²`; first derivatives of distances are bounded, and the possible second-derivative singularities `1/r`, `1/s`, and `1/u` are locally square integrable in their three normal dimensions. The Coulomb Hamiltonian action is square integrable. Coordinate formulas below hold away from collision sets, which have measure zero.

A straightforward nested trial family is the span of

    exp[−alpha(r+s)] (r^i s^j+r^j s^i) u^k,
    0<=i<=j, k>=0, i+j+k<=Omega,

using just one copy when `i=j`. The dimensions are 50 for `Omega=6`, 95 for `Omega=8`, and 161 for `Omega=10`. These are suggested exploratory sizes, not proven sufficient sizes for the requested variance. A small variational energy error does not establish a small residual. A rational alpha near an optimized value can be fixed before certification.

## 2. Hamiltonian action

For a differentiable function `F(r,s,u)`, define

    Cr=(r²+u²−s²)/(ru),
    Cs=(s²+u²−r²)/(su).

Then

    (Δx+Δy)F = Frr+Fss+2Fuu+2Fr/r+2Fs/s+4Fu/u
                 +Cr Fru+Cs Fsu.

For example, the mixed coefficient follows from
`2 gradient_x r · gradient_x u = Cr`. Geometrically `|Cr|,|Cs|<=2` on the physical triangle domain, although expanding them into monomials introduces reciprocal powers.

Writing `H Phi=exp[−alpha(r+s)] Q`, direct differentiation gives, for general nuclear charge `Z`,

    Q = −(Prr+Pss+2Puu)/2
        +(alpha−1/r)Pr+(alpha−1/s)Ps−2Pu/u
        −Cr Pru/2−Cs Psu/2+alpha(Cr+Cs)Pu/2
        −alpha² P+(alpha−Z)(1/r+1/s)P+P/u.       (Action)

This expression can be evaluated as a finite Laurent polynomial using exact rational coefficients. Every exponent of `r,s,u` appearing in `Q` is at least `−1`: a potentially more negative derivative contribution has a zero derivative coefficient. Combine identical Laurent monomials before forming products. A derivative term with coefficient zero must be dropped rather than evaluated with a spurious singular exponent.

Consequently the norm integrand `P²`, energy integrand `P Q`, and squared-action integrand `Q²` reduce to the moments in §3. The first two have nonnegative exponents **after including the measure factor**. The squared-action moments have exponents at least `−1` after including that factor.

## 3. A general exact moment formula

Rotational integration gives

    ∫_(R³×R³) f(r,s,u) dxdy
       =8 pi² ∫_(r,s>0, |r−s|<u<r+s) r s u f(r,s,u) dr ds du.

Define the reduced moment, without the common `8 pi²`, by

    I(a,b,c;kappa)=∫_triangle exp[−kappa(r+s)] r^a s^b u^c dr ds du,

for integers `a,b,c>=−1` and positive rational `kappa`. Require `a+b+c>−3`. These conditions make the following integrals finite. Every moment arising from (Action) and the stated polynomial basis satisfies the radial integrability requirement.

Substitute

    t=r+s, x=(r−s)/(r+s), v=u/(r+s),
    r=t(1+x)/2, s=t(1−x)/2, u=t v.

The domain is `t>0`, `−1<x<1`, `|x|<v<1`; the Jacobian is `t²/2`. Let `d=a+b+c`. Then

    I(a,b,c;kappa)
       =2^(−a−b−1) (d+2)! / kappa^(d+3) · A(a,b,c),             (Moment)

where

    A(a,b,c)=∫₀¹ Wab(x) Jc(x) dx,
    Wab(x)=(1+x)^a(1−x)^b+(1−x)^a(1+x)^b,
    Jc(x)=(1−x^(c+1))/(c+1)       when c>=0,
    J_(−1)(x)=−log x.

This formulation integrates the radial scale exactly. It also preserves the cancellation at `x=1` before integrating any potentially divergent angular pieces.

### 3a. Both a and b nonnegative

Expand the finite polynomial `Wab(x)=sum_n w_n x^n` using exact integers. Then

    A(a,b,c)=sum_n w_n/[(n+1)(n+c+2)]        for c>=0,
    A(a,b,−1)=sum_n w_n/(n+1)².

The first formula follows by integrating `x^n(1−x^(c+1))/(c+1)`; the factor `c+1` cancels algebraically. The second uses `∫₀¹x^n(−log x)dx=1/(n+1)²`. These moments are rational.

### 3b. At least one of a,b is −1

Let `m=max(a,b)>=−1`. The exact rational-function identity is

    Wab(x)=2 sum_(j=0)^floor((m+1)/2) binom(m+1,2j) x^(2j)/(1−x²).

It remains valid when `a=b=−1`, with the sum consisting of its `j=0` term. Therefore

    A(a,b,c)=2 sum_j binom(m+1,2j) B(2j,c),
    B(n,c)=∫₀¹ x^n Jc(x)/(1−x²) dx,       n even, n>=0.

The integrand is finite in the integrated sense: `Jc(x)` vanishes linearly at `x=1`, including the case `c=−1`. Never split it into separately divergent integrals.

For `c>=0`, put `q=c+1`.

If `q=2h` is even,

    B(n,c)=[sum_(ell=0)^(h−1) 1/(n+2ell+1)]/q.

If `q=2h+1` is odd,

    B(n,c)=[sum_(ell=0)^(h−1) 1/(n+2ell+1)+L_(n+2h)]/q,

where the empty sum is zero and

    L_0=log 2,
    L_(j+2)=L_j−1/[(j+1)(j+2)]       for j even, j>=0.

These follow from finite polynomial division:

    (1−x^(2h))/(1−x²)=sum_(ell=0)^(h−1) x^(2ell),
    (1−x^(2h+1))/(1−x²)=sum_(ell=0)^(h−1)x^(2ell)+x^(2h)/(1+x),

and `L_j=∫₀¹x^j/(1+x)dx`.

For `c=−1` and `n=2j`, the positive geometric series gives

    B(2j,−1)=sum_(ell=j)^infinity 1/(2ell+1)²
             =pi²/8−sum_(ell=0)^(j−1)1/(2ell+1)².

Tonelli justifies the geometric-series integration. The last equality uses the classical reciprocal-square sum `sum_(n>=1)1/n²=pi²/6`; this analytic identity is part of the trusted human derivation unless separately formalized. A fully rational alternative is to bound the displayed positive odd-square tail directly, but its crude convergence is too slow for high-precision certification. A faster rational proof can enclose `pi` and use the established identity.

Thus every reduced moment lies in

    Q + Q log 2 + Q pi²,

multiplied by the rational radial factor in (Moment). Contrary to a tempting simplification, the squared Hamiltonian action need not reduce to rational numbers and logarithms alone.

## 4. Assemble the certificate with only rational endpoints

Fix rational coefficients of `P` and rational `alpha`, and set `kappa=2alpha`. Define reduced exact quantities

    S = <Phi,Phi>/(8pi²),
    H1 = <Phi,H Phi>/(8pi²),
    H2 = <H Phi,H Phi>/(8pi²).

The norm `S>0` and `H1` are rational, because their moment exponents after the measure are nonnegative. The quantity `H2` is an exact rational linear combination of `1,log2,pi²`. Therefore

    a = H1/S

is the **exact rational** Rayleigh quotient of the chosen trial state. No floating-point eigenvalue from the exploratory optimization is used as the certified energy. The normalized residual variance is

    variance = H2/S − a² >=0.

Use rational outward intervals for `log2` and `pi²`. For example,

    log2 = 2 sum_(n=0)^infinity (1/3)^(2n+1)/(2n+1),

and after `K` terms (`n=0,...,K−1`) the positive remainder is at most

    9/[4(2K+1)3^(2K+1)].

Machin's arctangent identity with alternating-series remainder bounds supplies rational bounds on `pi`; positive interval squaring supplies bounds on `pi²`. Apply coefficient signs correctly when combining these intervals. All final enclosure endpoints are rational.

An implementation can cache each moment as a triple of rational coefficients for `(1,log2,pi²)`. All trial coefficients are rational, so the quadratic forms preserve this linear representation; there is no need for a general symbolic-expression system. Norm and energy matrices can be cached as pure rational matrices. Certifying one fixed optimized vector is cheaper than interval-enclosing every eigenvalue of every variational matrix.

## 5. Why the Temple threshold −5/2 is a continuum statement

Let `Hfree` be the sum of the two charge-two hydrogenic one-electron Hamiltonians, on the full fermionic two-electron spin space. Its unique lowest determinant occupies `1s up` and `1s down`, with energy `−4`. The next one-electron principal level has energy `−1/2`, while the `1s` level has energy `−2`. Hence its second fermionic min-max level is `−5/2`. The positive electron–electron repulsion gives the quadratic-form order

    H >= Hfree,

so the second min-max level of the full continuum helium Hamiltonian is at least

    beta = −5/2.

This uses the full spectral structure of the charge-two hydrogenic operator, including its continuum threshold, rather than a finite matrix comparison. That hydrogen spectral theorem and the min-max principle remain human/theorem-library dependencies until explicitly formalized. A normalized trial state with `a<beta` establishes a spectral value below beta and isolates the unique ground level there. The Coulomb operator's standard self-adjointness and discrete-spectrum facts are also required.

Temple's inequality now gives

    a − variance/(beta−a) <= E0 <= a.

For completeness, the spectral measure proof is short. Above the ground point `E0`, the spectral support lies at least at `beta`, so the operator polynomial `(H−E0)(H−beta)` is nonnegative. Its expectation in the trial state is

    variance+(a−E0)(a−beta) >=0.

Since `a<beta`, rearranging gives `a−E0 <= variance/(beta−a)`. The upper bound is variational.

If a rational certified bound `Vplus>=variance` is available, the final **rational continuum certificate** is

    [ a−Vplus/(beta−a), a ].

Its width is at most `10^(−6)` exactly when

    Vplus <= (beta−a)/10^6.

Near the physical helium ground energy the denominator is approximately `0.4`, so the exploratory target is a variance below approximately `4·10^(−7)` Hartree². This approximate target is only guidance; the final comparison uses the exact rational `beta−a`.

## 6. Implementation and trust boundaries

1. Optimize alpha and coefficients using ordinary high-precision numerical linear algebra if useful. Improve the basis until the residual, not just the energy, is promising.
2. Freeze rational alpha and rational coefficients. Recompute `S,H1,H2` from the exact moment formulas. Reject `S<=0` or `a>=−5/2`.
3. Bound `log2` and `pi²` with sufficiently narrow rational intervals and produce `Vplus` outward. Check the final rational width.
4. Save the exact coefficients, rational moment expressions or their replayable construction, constant bounds, norm, Rayleigh quotient, variance enclosure, Temple threshold, and final endpoints.
5. Separately label what Lean proves. A Python calculation with integer/Fraction arithmetic is a reproducible rigorous-arithmetic computation conditional on its implementation and analytic formulas; it is not automatically a Lean-kernel certificate. A Lean theorem accepting `S,H1,H2` or the variance bound as hypotheses verifies only the subsequent implication unless those inputs are themselves certified inside Lean.

High-order monomial Gram matrices can be ill-conditioned. Scaling basis elements and using high precision may help exploratory optimization, but does not excuse a final interval that fails its width test. Cancellation in the exact Laurent expansion is handled with rational arithmetic. Endpoint cancellation in singular moments must be handled by the formulas in §3b before integration.
