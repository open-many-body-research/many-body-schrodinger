> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Schwartz candidate C: finite-domain and moment gate

**PROVEN (existing paper).** Schwartz, arXiv:math-ph/0605018, equation (0.3), specifies
`exp(-k*S/2) S^l (U/S)^m (T/S)^n (log S)^q`, where
`S=r1+r2`, `T=r1-r2`, `U=r12`, `l,m>=0`, `n>=0` even, `l+m+n<=N`,
and `q=0,1`. Its fixed `k=2` means `exp(-S)`, not `exp(-2S)`.
The earlier directly cited arXiv:physics/0208004 discusses omitting the three
low-order logarithmic terms and a table-counting discrepancy. This experiment
uses the full displayed dictionary, explicitly retaining all three terms.

Its dimension is `2 sum_(j=0)^floor(N/2) binom(N-2j+2,2)=O(N^3)`.
The numerical basis is divided by `l!` and multiplied by a rational power of two
to bring its diagonal overlap approximately into `[1/2,2]`. These scalings are
frozen in every matrix JSON; they change the regularization penalty, not the
span. Scales are chosen empirically and subsequently used as exact rationals.
The indices have logarithmic bit height and the factorial has `O(N log N)` bits.
No coefficient-height or uniform conditioning theorem is asserted.

## Operator-domain membership

**PROVEN (this session).** Every finite displayed term is in physical spatial
`H^2(R^6)`. On a unit hyperradial annulus, `S` is bounded away from zero; the
ratios and logarithms there have second derivatives bounded by a constant times
`1+1/r1+1/r2+1/U`. These binary-collision singularities are square integrable in
their three transverse dimensions. This uses the same weak distance-derivative
calculus as the existing plain-Hylleraas domain proof.

At the triple collision, the nonlogarithmic factor has total homogeneous degree
`l`, regardless of the written power `S^(l-m-n)`. Scaling annuli gives a squared
Hessian integral bounded by a constant times
`integral_0^epsilon rho^(2l+1)(1+|log rho|^2) d rho`, finite for `l>=0`.
Origin cutoffs converge in `H^2`: their second-derivative error is bounded in
norm by `C epsilon^(l+1)(1+|log epsilon|)`. Thus no distribution supported at the
origin remains. The exponential controls infinity. Multiplying by the spin
singlet gives an antisymmetric operator-domain trial because `n` is even.

This check covers even the angularly discontinuous `l=0` ratios and `log S`.
It does not license unrestricted negative powers: a generic term with total
homogeneous degree at most `-1` fails the radial Hessian integrability test.

## Exactly separated moment family

**PROVEN (this session).** Expand only `T^n`, retaining powers of `S` explicitly.
Sparse algebra terms are indexed by `(r1 power,r2 power,U power,S power,log depth)`.
First and second derivatives use the ordinary product and chain rules. The
existing distance-coordinate Hamiltonian formula then gives the full function
`H phi`, including terms outside the dictionary. The log depth remains at most
one; a product of two actions has log depth at most two.

After including the rotational measure, the required moments are

`I(a,b,c,d,q)=integral_triangle exp(-2S) r1^a r2^b U^c S^d (log S)^q dr1 dr2 dU`,

with `a,b,c>=-1`, `q<=2`, and `nu=a+b+c+d+2>=1` for squared-action terms.
Substitute `r1=S(1+t)/2`, `r2=S(1-t)/2`, `U=S*w`, with
`-1<t<1`, `|t|<w<1`. The moment separates as

`I=2^(-a-b-1) A(a,b,c) R(nu,q)`.

Here `A` is precisely the existing endpoint-safe angular integral in
`helium/THEORY.md`, and
`R(nu,q)=integral_0^infinity exp(-2S) S^nu (log S)^q dS`.
Writing `h_n=sum_(j=1)^n 1/j`, `h2_n=sum_(j=1)^n 1/j^2`, its values are

`R(n,0)=n!/2^(n+1)`,

`R(n,1)=R(n,0)(h_n-gamma-log 2)`,

`R(n,2)=R(n,0)((h_n-gamma-log 2)^2+pi^2/6-h2_n)`.

Thus the exact constant ring is `Q[gamma,log 2,pi^2]`. The module stores finite
polynomials in these constants with exact rational coefficients. This is larger
than the old three-dimensional vector space `Q+Q log 2+Q pi^2`.

No unverified special-function formula is necessary. Define
`gamma=-integral_0^infinity exp(-t) log t dt`. For
`K=integral_0^infinity exp(-t)(log t)^2 dt`, the substitution
`x=v*z`, `y=v*(1-z)` gives

`2(K-gamma^2)=integral_0^1 log^2(z/(1-z)) dz=2 zeta(2)`.

For the last equality, expand the positive series for `-log(1-z)` to obtain
`integral_0^1 log z log(1-z) dz=sum_(j>=1) 1/[j(j+1)^2]=2-zeta(2)`.
The two pure log-square integrals each equal two. The already used Basel
identity gives `zeta(2)=pi^2/6`. Integration by parts for integer powers yields
the three displayed radial formulas; its endpoint terms vanish. Finally the
substitution `t=2S` introduces `log 2`.

Gamma is enclosed by `rate_decision/gamma_interval.py`, integrating a rational
Taylor polynomial on `[0,T]` and bounding both its integrated absolute remainder
and the tail explicitly. All final arithmetic is outward dyadic rational
arithmetic using the existing interval engine.

## Selection, certification and audit

**EMPIRICAL.** Candidate selection uses 90-digit Decimal inverse iteration on
`(Q+10A+25G+2^(-160) I,G)`, the corrected fixed shift `sigma=-5`. The iteration
starts at the first basis vector and uses 160 iterations. No reference ground
energy appears in selection, acceptance, or certification. The strict filter is
`mean<=-11/4`. The full raw matrices, rational coefficients, precision, pivots,
pencil residual, elapsed time, package versions, and hashes are retained.

**PROVEN (this session).** The certifier recomputes the rational selected vector's
moments both by pairwise matrix contraction and by combining the actual
functions before applying `H`; equality of the resulting exact polynomial
expressions is asserted. Interval LDL proves the selected regularized quotient
is within the additive tolerance `10^(-16)` of the finite pencil minimum.
The continuum Temple separator is the existing `-5/2`. Mean and variance are
enclosed, rather than treating a log-dependent mean as rational.

Graph residual squared is enclosed by
`[v_lower, v_upper+(m_upper-ell)^2]`. The shifted-objective excess uses the same
certificate's `[ell,u]` to enclose `(E+5)^2`; no external energy is an input.

An independent exact action audit differentiates the Cartesian expression using
six-variable second-order jets, at `x=(3,0,0),y=(0,4,0)`. All 100 dictionary terms
through order six agree in `Q[log 7]` with the separate distance-coordinate
action. The exact constant-function norm and energy numerator are also checked
against product-orbital integrations. **EMPIRICAL:** thirteen independent
75-digit adaptive-quadrature moment diagnostics check the angular recurrence
and the radial log formulas. Those floating-point diagnostics are not inputs
to a certificate.

## Remaining approximation obligations

**OPEN.** A graph approximation theorem for the physical ground eigenfunction,
including all collision structure and behavior at infinity, is still needed.
The local quadratic Fock logarithm alone is not such a representation theorem.
The explicit finite moments and dictionary dimensions do not prove stable
approximant coefficient heights or polynomial precision cost for the full loop.
No RATE conclusion or Theorem T is asserted here.
