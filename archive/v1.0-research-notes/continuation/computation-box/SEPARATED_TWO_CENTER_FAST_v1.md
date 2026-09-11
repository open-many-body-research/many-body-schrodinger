> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A polynomial-cost separated two-center energy class

This theorem is for one electron and exactly two distinct fixed nuclei with
positive rational charges and rational three-dimensional coordinates. It is
a precisely restricted fast path, separate from the general molecular solver.
The requested output is a rational interval for the electronic spectral
infimum with width at most 2^(-p), where p is a nonnegative integer requested
bit count. The electron retains both spin components and the continuum
Hamiltonian is -Delta/2-z_L/|x-a_L|-z_R/|x-a_R| on the actual weak H2 domain.
The associated H1 form and its equality with the spectral infimum use the
paper molecular realization dependency in MOLECULAR_COMPUTABILITY_v1.md.
This result and Python implementation are not claimed to be Lean verified.

## Exact class, algorithm and correctness

Write z=max(z_L,z_R), d=|a_L-a_R|/2>0. The proved linear-partition IMS
corollary in TWO_CENTER_IMS_v1.md gives

    -z^2/2-z/d-pi^2/(32d^2) <= E_el <= -z^2/2.

The lower bound is a form inequality for every H1 spinor. For the upper bound
choose a single spin component of the normalized exponential
(z^3/pi)^(1/2) exp(-z|x-a|) centered at the stronger nucleus. It lies in H1,
has one-center form value -z^2/2 by direct radial integration, and the other
attractive Coulomb expectation is finite and nonpositive by translated
Hardy. Thus neither attainment of the molecular infimum, uniqueness, binding
nor a spectral gap is used. No hydrogen energy digits are an oracle.

For any rational 0<d_lo<=d, pi^2<16 gives the explicit interval

    I(d_lo)=[-z^2/2-z/d_lo-1/(2d_lo^2), -z^2/2].

The exact strict inequality pi^2<16 is weaker than the pi bounds already
proved/checked in the predecessor; the runtime needs no transcendental
evaluation. Both inverse-distance error terms decrease with d_lo.

The executable computes the exact rational q=d^2, k=floor(log2 q),
e=floor(k/2), and d_lo=2^e. These are implemented by numerator/denominator
bit lengths and at most one rational comparison, with exact floor division
also for negative k. The square witness is

    d_lo^2 <= q < 4d_lo^2,       d/2 < d_lo <= d.

It then computes W=z/d_lo+1/(2d_lo^2) and epsilon=2^(-p). Its accepted input
class is exactly the finite rational inputs satisfying W<=epsilon for this
specified d_lo. On that class the procedure returns status ACCEPTED and
I(d_lo), and fulfills the requested output. All permitted inputs terminate
with either ACCEPTED or DECLINED. A DECLINED receipt still contains a valid
coarse interval but does not claim requested precision.

A simple sufficient test, also emitted in the certificate, is

    d_lo >= 2^(p+1) z,       d_lo^2 >= 2^p.

Each condition allocates half the width budget to one error term. Thus the
following direct geometric condition guarantees acceptance:

    d >= 2 max(2^(p+1) z, 2^(ceil(p/2))).

Indeed d_lo>d/2 is at least each displayed threshold. This is a class whose
required separation grows with requested precision. A fixed molecule at
fixed finite separation is not thereby solved for every p by this fast path.
The large-p demonstrations below intentionally vary the exactly represented
nuclear geometry with p. They establish useful performance within this
explicit dissociation regime, not high precision at a fixed chemical geometry.

The general `molecular_box_v1.py` requested-width procedure remains a separate
universal fallback with its previously proved exponential cost. The fast
path never starts its enormous conservative schedule implicitly. Composition
may call that solver after DECLINED, but the polynomial claim covers only
the fast computation and accepted separated class.

## Input representation and operational bit cost

Input nuclei use a JSON list of exactly two objects, each with a center list
of three rationals and a positive charge. Each rational is an explicit JSON
integer or a string matching a signed decimal integer or such an integer
divided by a positive decimal integer. Scientific notation, finite-decimal
strings, floats and booleans are rejected. Leading zeros are rejected in
fraction-string numerators and denominators, apart from zero itself. No
compressed exponent syntax such as `1e1000000` is admitted. The source
disables the Python decimal integer conversion cap before parsing large
input or writing output; this is explicit runtime policy, not an assumption
that the default interpreter handles arbitrarily long decimal integers.

Let L be the actual input encoding length for the nuclear data, in bits or
characters up to a fixed constant factor; include syntactic padding if
present. Numerator and denominator bit lengths of each decoded rational are
O(L), since the decimal representation is explicit. There are exactly eight
input rationals. Charges are unrestricted positive rationals, including
very small ones. Let s=L+p+1. The following is a conservative classical bit
cost bound using schoolbook integer multiplication/division and Euclidean
gcd; faster library arithmetic may improve observed cost.

* Parsing a total of O(L) decimal symbols by repeated base-ten accumulation
  costs O(L^2); gcd normalization is bounded by O(L^3). There are only a
  constant number of nuclear rationals, so no growing list is hidden.
* Three coordinate differences, their squares, a three-term sum and division
  by four use only O(1) rational operations. Even unrelated input denominators
  give O(L)-bit numerators and denominators because this count is constant.
  Distinctness makes q>0. Exact comparison and sorting two centers cost
  polynomial time with O(L)-bit operands.
* The numerator/denominator bit-length difference gives k or k+1. A single
  comparison with 2^k corrects it. Since q has O(L)-bit numerator and
  denominator, |k| and |e| are O(L). The rational powers used for d_lo have
  O(L) bits, including for separations below one. No repeated search in
  physical distance or root approximation is required.
* The fixed number of energy/width rational operations retain O(L) bits.
  Constructing epsilon=1/2^p takes O(p+1) bits and time. Cross multiplication
  for exact width and sufficient-condition tests uses O(s)-bit operands.
  Writing p from its binary encoding is also bounded by this accounting.
* Every certificate rational has O(s) bits and there are O(1) such fields.
  Decimal integer output by long division has O(s^2) cost. The JSON and
  source hash metadata have constant field count, and the source itself is
  fixed independently of the physical input. A hash/source-read cost is
  therefore a fixed additive constant. Parsing the emitted certificate and
  rechecking it has the same polynomial bound.

Consequently O(s^3) bit operations and O(s^2) workspace are safe upper
bounds for this actual finite procedure, including parsing, certificate
emission and replay. This intentionally loose workspace bound includes
schoolbook arithmetic temporaries; the live rational values themselves use
O(s) bits. With p represented in binary this is polynomial in the numeric
requested precision p, not an all-input claim polynomial in log p. Output
and input sizes are counted explicitly, including the separation growth
addressed below.

There is a stronger encoding observation on accepted inputs. Regardless of
how small the charges are, the IMS term forces d_lo^2>=2^(p-1). If q=A/B
in reduced form with positive integers A,B, then A>=q>=2^(p-1), hence
p<=bit_length(A)=O(L). (For p=0 the same final inequality is immediate.)
Thus the accepted class has polynomial cost in its ordinary explicit input
length even when p itself is binary encoded. Shrinking charges can ease the
Coulomb separation threshold but cannot remove this IMS separation growth.
For declined inputs with arbitrarily large p relative to L, the procedure
still emits epsilon explicitly using p+1 bits; the all-input bound remains
polynomial in numeric p and is not claimed polynomial in log p.

The extra independently implemented certificate checker verifies integer
cross-multiplication witnesses without importing the producer. This reduces
shared implementation dependence; both programs still trust ordinary Python
integer semantics and the paper continuum theorem. No complexity or runtime
claim here is a Lean theorem.

## Preservation and evidence record

`separated_two_center_fast_v1.py` is new and does not alter the IMS source or
any old molecular certificate. Concrete high-p inputs, rational outputs,
timing, memory, exact width checks and isolated source-only replay are
recorded in SEPARATED_TWO_CENTER_EXECUTION_v1.md. External reference energies
are not used. The predecessor TWO_CENTER_IMS_v1.md has SHA-256
355910471e5c2671bc3ce49d13c9f7f102e8ef6da87760f407fa3a131866ac2c.
Frozen baseline commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660 and
tag theorem-t-proof-freeze-2026-09-09 remain unchanged.
