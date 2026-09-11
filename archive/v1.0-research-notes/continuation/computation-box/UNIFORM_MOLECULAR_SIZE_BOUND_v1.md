> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit uniform size dependence of the molecular algorithm

This is an additional paper bit-complexity analysis of the exact algorithms
in `MOLECULAR_COMPUTABILITY_v1.md`, not a new Hamiltonian or an improved
practical implementation. It makes the previously fixed-input constants
visible. The physical continuum link and implementation trust boundary are
unchanged; no Lean bit-cost theorem is claimed.

## Input size and claim

Represent each nuclear charge and coordinate by a signed integer numerator
and positive integer denominator in binary. Let L>=1 be the total length of
the finite nuclear list, including those numbers, the nucleus count, and
delimiters. Thus the number of nuclei is <=L and L dominates the sum of the
binary lengths of all supplied numerators and denominators. A concrete JSON
encoding with additional redundant text can be charged its actual length;
the canonical binary mathematical input is the model used here.

For integers N>=0,p>=1, the deterministic bit-cost upper bound is

    2^O((N+1)(p+N+L+1)),

with a universal implicit constant in the declared schoolbook integer model.
It includes constructing the full finite certificate and replaying it, and
applies to either the electronic energy or the fixed-nucleus total energy.
This is **not** polynomial precision or growing-system efficiency. Since
the numerical electron count N and precision p are integers, the displayed
bound is not polynomial in their binary encoding lengths either.

The distinction N=0 matters: its electronic energy is zero, but reading the
nuclear input and computing nuclear repulsion still depend on L and p. The
factor N+1 avoids falsely assigning constant cost to that branch.

## Explicit bounds for a positive-electron localization level

Set S=p+N+L+1 and assume N>=1. All following powers of two have universal
exponents. Write Q=ceil(sum z_l) and A=max_l sum_j |a_l,j|. Since each input
numerator magnitude is smaller than its represented power of two, summing
positive terms gives Q<=2^L and A<=2^L. A nonzero coordinate difference of
distinct nuclei is at least 2^-L: its denominator divides the product of
the two supplied denominators, whose total bit length is at most L. Hence
each nuclear separation is >=2^-L. Using 2^-O(L) instead would suffice.

At any level k=1,...,N the effective precision is p_k=p+3(N-k), so
t=epsilon_k^-1=2^(p_k+3)<=2^(p+3N). The implemented radius

    R=t k(2Q+1)+2A

therefore satisfies R<=2^(4S). Its rational denominator has at most L bits,
and its numerator at most 5S bits: forming a sum of coordinate absolute
values introduces only the product of the supplied denominators, and the
remaining summand is an integer. Neither the value bound nor its rational
encoding cost is omitted.

The smallest anchor cube has cutoff at most N and its kinetic index sum is
at most 3N^3. Consequently

    U0 <= 3N^3,
    K_kin=2(U0+kQ^2) <= 8N^3Q^2 <= 2^(5S).

Here K_kin denotes the common kinetic expectation bound, not the orbital
cutoff K. The clipping coefficient 2Q+k-1 is at most 3NQ. The actual ceiling
in the schedule gives

    M <= 256 N^4 Q^3 t <= 2^(8S),
    B=M[kQ+k(k-1)/2] <= 2^(11S),
    eta^-1=8t <= 2^(3S).

For the next estimate, a stronger intermediate is useful:
kQ+k(k-1)/2<=N^2Q, so B<=256N^6Q^4t<=2^(9S). The weaker displayed 2^(11S)
bound remains valid wherever it is used later. Also U0<=2^(4S), and S>=4.
The cutoff is chosen using
rhs=(U0+B+B^2/eta)32R^2/9. The stronger bound gives
rhs<=12*2^(29S)<=2^(30S)<=2^(34S). Thus all summation constants and the 32/9
factor are explicitly absorbed. The floor-square-root/ceiling
step and the anchor maximum give K<=2^(18S). These estimates deliberately
have slack for all ceilings and N=1, not just asymptotically large inputs.
The spin-orbital capacity C=2K^3 and matrix dimension m obey

    C <= 2^(55S),
    m=binom(C,k) <= C^k <= 2^(55NS).

The spatial coefficient D=4RM^2[kQ+2k(k-1)] is <=2^(24S), and
e^-1=32t<=2^(4S). Taking J0=ceil(4Dm/e) yields J0<=2^(84NS).
Local node resolution uses J* = J0+K^12, so

    J* <= 2^(217NS).

In particular no lcm(1,...,K) exponential is being hidden in these bounds.
The at-most-twelve local scalar indices have LCM<=K^12 even when pairwise
coprime. There are at most L K^6 nuclear cache entries and K^12 pair entries.

The explicit arithmetic coefficient from the local-grid proof is

    A_err=2^20 m(k+1)^2(Q+k+1)(M+1)^2(J*+1)^6(K+1)^2.

The bounds just proved give log2 A_err<=1427NS. Thus the sufficient precision
max(32,ceil log2(4A_err/e),ceil log2(2M),ceil log2(4096J*)) is <=1432NS.
The next actual doubling step is <=2864NS (and hence <=4096NS). This bounds
the **executed acceptance loop**, not merely an unspecified convergence rate.

For the midpoint eigenvalue bisection, Tmax<=N K^2<=2^(37S). Gershgorin's
initial width is at most 2m(Tmax+B+e), while tau^-1=8t<=2^(3S). Exact halving
therefore requires at most 128NS PSD decisions. The extra cases with an
already zero initial width only reduce this count.

## All arithmetic and loop costs

The displayed finite construction bound in `LOCAL_GRID_AND_BIT_COST_v2.md`
is polynomial in K,m,J*,N and the bit lengths of all scalar inputs, with
universal degree. The molecular extension multiplies the nuclear-integral
count by at most L and adds the coordinate/charge bit lengths. All of these
variables have either value <=2^O(NS) or bit length O(NS). In particular:

* Exact Machin, Taylor, factorial, rational-angle, square-root and reciprocal
  operations have the polynomial operand bounds detailed in the local-grid
  proof. Translated coordinate arithmetic adds only the actual nuclear input
  lengths. Local LCMs use at most twelve indices each.
* Dyadic cell masses and potential bounds give common denominators through
  accumulated cell sums. The rational nuclear charges add a common factor
  dividing the product of their given denominators, at most L additional
  bits. Repeated matrix terms do not create a new independent copy of that
  factor. Final rounding restores the common dyadic matrix denominator.
* PSD Schur intermediates are ratios of minors of one rational matrix with
  a common denominator. Hadamard bounds give at most
  O(m(b+q+log m+L)) operand bits, where b and q are the proved precision and
  bisection bounds. This can be exponentially many bits in the system
  parameters; it has not been replaced by a unit-cost arithmetic assumption.
  The q O(m^3) rational updates have the already stated polynomial bit cost
  in these explicit sizes.
* The complete occupation enumeration and creation/annihilation loops, all
  quadrature cells, worst-case linear cache lookups, matrix storage, and
  source/certificate serialization have polynomial bounds in the same size
  variables. Persisting caches and precision doubling are charged the safe
  squared-log overhead. There are N localization levels. These factors keep
  the total within 2^O(NS).

The number of rational certificate endpoints is at most a polynomial in m
and the integral/basis counts, each with bounded encoded bit length as above.
The full certificate size, including nested localization stages and saved
precision-attempt summaries, is therefore 2^O(NS). Decimal JSON conversion
can be implemented with polynomial bit cost and its digit cap is disabled
in the declared runtime; it is not an uncharged oracle.

For nuclear repulsion there are at most L^2 pairs. Their charges are bounded
by 2^L and separations below by 2^-L. Square-root and reciprocal precision
O(p+L) suffices for the requested total width. Exact summation may accumulate
unrelated reciprocal denominators, but there are at most L^2 of them: their
total bit length is polynomial in p+L. It would be incorrect to call that
sum dyadic before the final outward rounding. Its resulting bit cost is
polynomial in p+L, and is included by 2^O((N+1)S). The N=0 branch has this same
bound, including parsing and checking the distinct input centers.

The separate total-energy routine calls the electronic one at p+1. Replacing
S by S+1 changes these upper bounds by a universal factor in the exponent
and hence preserves the claimed 2^O((N+1)(p+N+L+1)) bound. Fresh checking runs
the construction again, so it has the same upper bound.

This explicit, large exponential dependence is compatible with difficult
growing-system instances. It asserts no complexity-theoretic collapse, no
efficient universal many-body solver, and no literature novelty. It only
removes previously unspecified finite-input dependence from this particular
certified energy construction, under its stated paper and runtime premises.
