> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Executed one-electron Coulomb box enclosure

Date: 2026-09-09. This is a new, deliberately restricted implementation branch.
Its evidence category is **exact-rational execution with a paper-level continuum
proof**, not Lean verification or a verified compiler/runtime theorem. It does
not discharge the arbitrary-N bounded-box obligation.

## Provenance and target

The frozen baseline is `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This branch does not modify its dictionary or
claim to implement its two-electron theorem.

The predecessor computational proposal is
`THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`,
SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.
Its entry-budget clarification is `QUADRATURE_BUDGET_CLARIFICATION_v1.md` in the
same directory, SHA-256
`11041c89b7b44500c14a9b5af82bbd366e19f7f342efe6cde84e0517ca7dd11e`.
Both remain unchanged.

Inputs are N=1, integer Z>=1, rational R>=1. The output target is the lowest
Dirichlet form energy of the **uncut** operator `-Delta/2-Z/|x|` on
`Omega_R=(-2R,2R)^3`, with form domain `H^1_0(Omega_R; C^2)`. The two spin
components are identical invariant blocks, so representing one spatial block
preserves the infimum of the full one-electron fermionic spin-space. Dirichlet
extension by zero is used only as a full-space *form* trial; it is not claimed
to preserve H² across the boundary.

The classical self-adjoint realization and variational/spectral identification
are paper dependencies here. They remain separate formal obligations in the
parent project. The computations below become formal continuum certificates
only after those foundations, all integration lemmas, and the implementation
are linked by actual proofs. No Lean axiom claim is made for this Python code.

## Exact interval primitives

`exact_box_v1.py` uses Python arbitrary-length integers and `Fraction` throughout
the mathematical path. Floats appear only in elapsed-time/environment reporting.
Intervals are closed rational intervals, with arithmetic endpoint extrema.
`I.dyadic(b)` floors the lower endpoint and ceilings the upper endpoint at
denominator `2^b`; this avoids uncontrolled non-dyadic denominator growth in the
matrix accumulation. It is directed rounding implemented by integer operations.

For rational s>=0, compute
`k=isqrt(floor(s*2^(2b)))`. Then `k/2^b <= sqrt(s) < (k+1)/2^b`, with equality
checked exactly for a square. Reciprocal interval endpoints are reversed; an
interval containing zero is rejected. For clipping, `s<=M^-2` returns M exactly;
otherwise square-root precision is increased if necessary to make its lower
endpoint positive, reciprocals are enclosed, and both endpoints are clipped.

Pi uses Machin's identity `pi=16 atan(1/5)-4 atan(1/239)` and the alternating
arctangent series: the sum through one term and the sum through the next bracket
the limit. This is a classical elementary identity, not reference digits.
For `sin(pi*r)`, rational periodicity/reflection reduces r to [0,1/2], with exact
special cases 0 and 1/2. The odd Taylor polynomial through degree `2j-1` has
remainder at most `|y|^(2j+1)/(2j+1)!`, since the even degree `2j` coefficient is
zero and every real sine/cosine derivative has absolute value<=1. Interval
evaluation includes the enclosure error in y. The coefficient/remainder loop
terminates because factorial growth dominates powers on the fixed interval.

These algorithms are inspectable mathematical procedures. Tests, CPython
execution and independent review do not turn their code into kernel proofs.

## Matrix integration with a proved spatial error

Let `phi_k(x)=(2R)^(-3/2) prod_a sin(pi*k_a*(x_a+2R)/(4R))`, with every component
of k in `{1,...,K}`. These are orthonormal; the represented dimension is `m=K^3`.
The clipped potential is `V_M=-Z min(1/|x|,M)`.

Split each coordinate into J equal cells. On each three-dimensional cell C,
exact rational minimum/maximum squared distances from the origin give an
outward interval `[v_-,v_+]` for V_M. Put `c=(v_-+v_+)/2` and
`delta=(v_+-v_-)/2`. For any two real orbitals,

`|integral_C (V_M-c) phi_a phi_b| <= delta*(W_aa(C)+W_bb(C))/2`,

where `W_ab(C)=integral_C phi_a phi_b`. This follows pointwise from
`2|phi_a phi_b|<=phi_a^2+phi_b^2`; it includes sign-changing products.

Each W is a product of three exactly integrated one-dimensional sine products.
In normalized coordinate t, its one-dimensional factor is

`2 integral_u^v sin(pi*k*t) sin(pi*l*t) dt = D(k-l)-D(k+l)`,

where `D(0)=v-u` and `D(h)=(sin(pi*h*v)-sin(pi*h*u))/(pi*h)` otherwise. Its rational
interval is obtained by the preceding primitives. Diagonal factors additionally
intersect the known interval [0,1]. The implementation sums `c*W_ab` with
interval arithmetic and adds the above nonnegative error using upper bounds on
W_aa,W_bb. The kinetic diagonal is `pi^2*sum(k_a^2)/(32R^2)` and is included in
the same final entry interval.

The potential is even in each Cartesian coordinate. If any k/l coordinate
parities differ, the corresponding compressed matrix entry is exactly zero.
For remaining entries the integrand and diagonal weights are even in each
coordinate; reflection-related cells have equal integrals and potential bounds.
The code evaluates one representative with integer orbit multiplicity. An odd-J
central cell is self-reflecting and has multiplicity one in that coordinate.
This is an exact symmetry reduction, not numerical cancellation.

Let A be the entrywise rational midpoint matrix. If E_ab is half the enclosing
entry width, symmetry gives `||A-H_P|| <= max_a sum_b E_ab = e`. Thus a rational
eigenvalue bracket `[l,h]` for A yields `[l-e,h+e]` for the true compression.

## Rational eigenvalues and the omitted continuum

`is_psd` performs exact rational symmetric Schur elimination. A negative
diagonal disproves PSD. A zero diagonal with a nonzero remaining offdiagonal
also disproves PSD, by restricting the quadratic form to those two coordinates.
A zero remaining row/column is removed. A positive pivot permits the usual
congruence to its positive scalar and its Schur complement. These cases exhaust
all possibilities, including singular PSD matrices.

Gershgorin gives a rational initial lower endpoint for the smallest eigenvalue
of A; its least diagonal entry is an upper endpoint. At each bisection midpoint
t, `A-tI` PSD is equivalent to `t<=lambda_min(A)`. Bisection terminates after
finitely many exact rational decisions for every positive rational tolerance.

Let P contain the stated sine modes and Q=I-P. For the full Dirichlet kinetic
operator, `QTQ >= Lambda Q`, where

`Lambda=pi_lo^2*((K+1)^2+2)/(32R^2)`.

Every omitted orbital has some coordinate index>=K+1 and both others>=1. Also
`||V_M||<=B=MZ`. For every eta>0, the offdiagonal estimate
`2|<u,V_M v>| <= eta||u||^2+B^2/eta ||v||^2` gives

`lambda_M >= min(lambda_P_lower-eta, Lambda-B-B^2/eta)`.

The upper bound is the minimum of the computed compression upper bound, each
computed diagonal-trial upper bound, and 16. The latter is a safe common upper
bound because the `(1,1,1)` trial has clipped energy at most its kinetic energy
`3pi^2/(32R^2)<1`. The deliberately loose constant 16 preserves the predecessor
schedule. Hydrogen completion of the square gives `q,q_M >= -Z^2/2`, and the
implementation also uses this independent lower bound.

## Restoring the true potential

The clipping error has one sign in this N=1 restriction: `q<=q_M`, hence
`lambda<=lambda_M`. The elementary inequality
`(1/r-M)_+ <= 1/(4Mr^2)` and Hardy give

`0 <= q_M[f]-q[f] <= (2Z/M) T[f]`.

The *unclipped* form satisfies `q>=T/2-Z^2`. If U is any common upper bound for
lambda and lambda_M, apply this to an **unclipped** normalized minimizing vector
(compact Dirichlet resolvent), obtaining `T<=2(U+Z^2)`. Evaluating q_M on that
vector yields `lambda_M <= lambda + 4Z(U+Z^2)/M`. Equivalently, approximate
minimizers give the same bound after sending their variational errors to zero.
Evaluating only the clipped minimizing vector would not prove this direction.

Thus, with the clipped enclosure `[a,b]`, the output

`[max(-Z^2/2, a-4Z(U+Z^2)/M), b]`

encloses the true Dirichlet energy. Zero extension and the elementary full-space
lower bound also give the reported full-space interval
`[-Z^2/2,min(0,b)]`. This full-space interval is often much wider than the exact
one-electron energy; its upper endpoint is actually obtained from box trials,
not inserted from a hydrogen energy formula or reference digits.

## Requested-width procedure and its limitation

The command `schedule` exposes all sizes without allocation. `box_enclose` is an
actual unrestricted Python procedure implementing the N=1 specialization of
the predecessor's conservative schedule. It has no silently imposed cutoff.
It sets `U=16`, `K0=2(16+Z^2)`,

`M=ceil(8*K0*2Z/epsilon), eta=epsilon/8, e=epsilon/32`,

then chooses K with `9(K+1)^2/(32R^2)>=16+B+B^2/eta`. Set `m=K^3`, `t=e/m` and
`J=ceil(16RZM^2/t)`. The radial clipping map has Lipschitz constant ZM². A cell
has diameter `4sqrt(3)R/J<8R/J`, so its exact potential half-range is at most
`4RZM^2/J<=t/4`. Since each orbital's cell masses sum to one, each matrix
entry's *limiting* spatial radius is at most t/4. On the fixed finite grid all
arithmetic interval errors tend to zero as precision increases. Therefore
doubling the interval bit precision until every entry radius is at most t
terminates with strict margin.

At that stage e_matrix<=epsilon/32. The complement condition implies
`lambda_M>=lambda_P_lower-eta`; clipping restoration is <=epsilon/8. The code's
output width is at most

`epsilon/8 + 2epsilon/32 + epsilon/8 + epsilon/8 = 7epsilon/16 < epsilon`.

The final explicit width assertion checks this consequence on any executed
requested-width run. No such conservative scheduled run is claimed here:
even `Z=1,R=2,epsilon=1/2` requests K=16412, dimension 4,420,633,646,528 and a grid
with over 10^63 cells. The stored schedule is reproducible evidence of this
implementation's prohibitive cost. Feasible runs select explicit parameters
and report the enclosure they achieve; they do not masquerade as scheduled
precision successes.

## Cost and trust boundary

For an explicitly chosen stage, matrix accumulation has at most J³m(m+1)/2
cell-entry updates, each involving a bounded number of exact rational interval
operations. Pi/sine computations are cached **within the current process** by
their mathematical arguments; no numerical disk cache is read. Parity and cell
reflection reduce the actual count. Accumulated potential terms have dyadic
denominators with at most a fixed multiple of the interval bit precision;
numerator lengths also include log J, log m and the potential bound. Kinetic
and transcendental enclosures are rational expressions with separately growing
operands; their evaluation and gcd costs cannot be unit-cost operations.

For the generated **dyadic** m-by-m midpoint matrix, rescale the shifted matrix
by its single common denominator (including the current bisection midpoint's
denominator), and let L bound the resulting integer numerator bit sizes and
that denominator's bit size. Schur-complement entries are ratios of minors.
Hadamard's determinant bound then gives operand size `O(m(L+log m))` bits.
This claim does not apply to arbitrary unrelated rational entry denominators
with L measured before common rescaling. Each PSD decision uses O(m³) rational updates; with a
conservative cubic bit bound for rational arithmetic, a valid non-optimized
bound for this *finite matrix stage* is `O(m^6(L+log m)^3)` bit operations per
decision, plus input formation. Bisection adds the logarithm of initial bracket
width divided by tolerance. This explicitly avoids a unit-cost claim.

No complete optimized whole-program bit-complexity theorem is supplied. The
required output matrix already rules out interpreting this schedule as
polynomial in p when epsilon=2^-p. No uniform efficiency, novelty, N>=2 solver,
general arbitrary-N implementation, original two-electron theorem, or Lean
implementation theorem follows from this branch.

## Reproduction and certificate path

Run from this directory with Python 3 and its standard library:

```sh
python3 -B test_exact_box_v1.py
python3 -B exact_box_v1.py run --J 64 --bits 32 --output new_certificate.json
python3 -B check_certificate_v1.py new_certificate.json
python3 -B exact_box_v1.py schedule --epsilon 1/2
```

Outputs use exclusive creation to preserve earlier certificates. The checker
verifies the exact source hash, recomputes every potential and kinetic matrix
entry in a fresh process, and recomputes all spectral/restoration bounds. It
shares the published arithmetic implementation; it is **not** a second
independently formalized kernel. Python, integer arithmetic, `Fraction`,
`math.isqrt`, the implementation, and the paper lemmas remain in its trust
boundary. The exact JSON rational endpoints, not printed decimal diagnostics,
are the certificate data.

The development smoke/J16/J32 files predate final source edits and retain their
original source hashes. They are development records, not final-source
reproducibility certificates. The final reproduction report explicitly names
the final-hash certificates and isolated-source reruns. See `EXECUTION_REPORT_v1.md`
for those results and independent review disposition.
