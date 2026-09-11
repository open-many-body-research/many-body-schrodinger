> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Two-electron Coulomb comparison on the actual full fermionic space

Evidence category: **paper proof**, including the actual Sobolev slicing,
projection maps and exact product-trial integral. Its last spectral conclusions
use the explicitly declared actual self-adjoint realizations and the previously
proved rank-one spectral mechanisms. The physical hydrogen complement and its
lifting in this file are not claimed to be Lean-verified. This new file does not
change the original approximation dictionary.

## 1. Model, domains and exact conclusions

Let Z>0, x,y in R^3, and use Lebesgue measure and counting measure on the four
ordered spin labels sigma=(sigma_1,sigma_2) in {up,down}^2. The full spin Hilbert
space is L2(R6;C^4), with inner product conjugate-linear in its first argument.
Its fermionic closed subspace consists of the almost-everywhere identities

    F_(sigma_2,sigma_1)(y,x) = -F_(sigma_1,sigma_2)(x,y).       (1)

The scalar and spin operators have the physical expression

    H_Z = -(Delta_x+Delta_y)/2 - Z/|x| - Z/|y| + 1/|x-y|.

The scalar domain is the actual weak H2(R6). The full fermionic domain is the
intersection of the componentwise actual weak H2 space with (1). The form domain
uses the analogous actual weak H1 intersection. Write q_Z for the real quadratic
form, with all four spin components summed in the spin case. Configuration Hardy
makes every displayed potential pairing finite. Pair repulsion is nonnegative.

Set

    phi_Z(x) = sqrt(Z^3/pi) exp(-Z|x|),
    Phi_Z(x,y) = phi_Z(x)phi_Z(y),
    chi_(up,down)=1/sqrt(2), chi_(down,up)=-1/sqrt(2),
    chi_(up,up)=chi_(down,down)=0,
    G_Z = Phi_Z chi,    beta_Z=-5Z^2/8,    C_Z=3Z^2/8.

Both Phi_Z and G_Z have norm one and belong to their intended H2 domains.
The physical comparisons proved below are, for every actual H1 input,

    q_Z[f] >= beta_Z ||f||^2 - C_Z |<Phi_Z,f>|^2              (2)

in the scalar space, and

    q_Z[F] >= beta_Z ||F||^2 - C_Z |<G_Z,F>|^2               (3)

in the full fermionic space. Equation (3) includes triplet and mixed spatial
symmetry components. It does not restrict inputs to a prescribed singlet sector.

For any alpha>0 the unit physical H2 trial G_alpha has the exact mean

    m_Z(alpha) = q_Z[G_alpha] = alpha^2-2Z alpha+5alpha/8.     (4)

Put

    Z_* = (20+5sqrt(10))/24.

For Z>Z_*, the choice alpha_*=Z-5/16 is positive and gives

    m_* = -(Z-5/16)^2 < beta_Z,
    d_Z = beta_Z-m_* = (96Z^2-160Z+25)/256 > 0.             (5)

Assume the actual scalar and full fermionic operators are self-adjoint and
semibounded on the stated H2 domains, with their actual spectral bottoms equal
to the infima of these H1 or H2 forms. These are realization premises for the
spectral assertions, not a redefinition of spectral energy. The full fermionic
premises are discharged in the audited continuum foundation; an application to
the scalar operator must separately supply its scalar realization.

Under these explicit realization premises, (2)--(5) and the rank-one spectral
mechanism give an attained simple ground energy E_Z in both spaces, with

    -Z^2 <= E_Z <= -(Z-5/16)^2 < -5Z^2/8,
    spec(H_Z) subset {E_Z} union [beta_Z,infinity),
    q_Z[w] >= beta_Z ||w||^2 whenever w is ground-orthogonal. (6)

The scalar and full fermionic ground energies coincide. The scalar ground
vector has a unique nonnegative unit representative, fixed by simultaneous
spatial rotations and exchange; multiplying it by chi gives the full fermionic
ground vector, unique up to complex phase. The separate reviewed strict-positivity
paper further makes the canonical scalar representative positive at every
configuration, including all collisions. Neither an ionization threshold nor
an assumed gap is substituted for the complement in (6).

The spectral statements here are paper-level physical instantiations. The final
formal physical hypotheses (2), (3) and (4) still require Lean proofs. A
noncomputable ground-eigenvector existence proof is not a procedure returning
coefficients of that eigenvector.

## 2. Actual Sobolev slices and one-electron energy bounds

The reviewed HYDROGEN_COMPLEMENT_REDUCTION_v2.md proves, for actual scalar
H1(R3) and every Z>0,

    (1/2)||grad h||^2-Z integral |h(x)|^2/|x| dx
       >= -(Z^2/8)||h||^2-(3Z^2/8)|<phi_Z,h>|^2.             (7)

Here is the precise slicing bridge used to apply (7). If f is in H1(R6), ordinary
compact smooth H1 approximation supplies f_n with sum_n ||f_(n+1)-f_n||_H1<infinity
and f_n to f in H1. For each y, take the H1(R3_x) norm of a difference of two
slices. Fubini gives

    integral ||f_(n+1)(.,y)-f_n(.,y)||_H1_x^2 dy
       = ||f_(n+1)-f_n||_2^2 + sum_j ||partial_(x_j)(f_(n+1)-f_n)||_2^2.

Minkowski's inequality and monotone convergence show that the sum of these
nonnegative slice norms is an L2 function of y, bounded by the sum of the
corresponding global H1 norms. Thus for almost every y the slices form a Cauchy
sequence in the complete weak H1_x graph. Their L2_x limits agree with f(.,y),
and their weak derivative limits agree with (partial_(x_j)f)(.,y): identify both
by their L2_y(L2_x) limits and Fubini. Consequently f(.,y) is actual H1_x almost
everywhere with those derivatives, and the integrated norm and derivative
identities above hold for f. This also proves the assertion with x and y
interchanged. Finite spin summation creates no exceptional-set difficulty.

The scalar coefficient

    A_1 f(y) = integral conjugate(phi_Z(x)) f(x,y) dx

exists absolutely for almost every y by Cauchy--Schwarz. It is measurable, lies
in L2_y and satisfies ||A_1 f||_2<=||f||_2. Measurability follows first for
truncated integrals and simple approximants and then by their almost-everywhere
limit. Sliced Hardy and Cauchy--Schwarz also give

    integral |f(x,y)|^2/|x| dx dy
       <= ||f||_2 ||f/|x|||_2 <= 2||f||_2 ||grad_x f||_2.

Every term in the integrated instance of (7) is therefore finite. Integrating
(7) over y and summing the four spin components gives

    e_1(F) >= -(Z^2/8)||F||^2-(3Z^2/8)||A_1 F||^2,          (8)

where e_1 is the full x kinetic-plus-nuclear form. The identical y calculation
gives (8) with e_2 and A_2. The scalar calculation simply has one component.
No slice of an H1 function was assumed smooth, and no punctured H2 core was used.

## 3. The physical projections, domains and commutation

Define bounded maps on the **ambient full spin space**, component by component,

    (P_1 F)_sigma(x,y)=phi_Z(x) A_1 F_sigma(y),
    (P_2 F)_sigma(x,y)=phi_Z(y) A_2 F_sigma(x).               (9)

Cauchy--Schwarz and ||phi_Z||=1 show their norms are at most one, and
||P_i F||=||A_i F||. Iterated integration shows P_i^2=P_i and
<P_i F,K>=<F,P_i K>; thus these are genuine orthogonal projections on the
physical L2 space. These identities use Fubini on absolutely integrable
products, justified by the same L2 bounds.

These maps also preserve the componentwise actual H1 and H2 spaces. For example

    partial_(x_j) P_1 f = (partial_j phi_Z) A_1 f,
    partial_(y_k) P_1 f = phi_Z A_1(partial_(y_k) f).          (10)

To prove the second identity, first test the weak derivative relation against a
compact y test and a compact approximation to phi_Z in L2_x, then pass to the
limit by Cauchy--Schwarz. The first is the product weak derivative identity.
The actual phi_Z belongs to H2(R3), as proved in the hydrogen branch. Applying
the same argument twice gives the xx, yy and ordered mixed second derivatives:

    (partial_j partial_k phi_Z) A_1 f,
    phi_Z A_1(partial_(y_j) partial_(y_k) f),
    (partial_j phi_Z) A_1(partial_(y_k) f),

respectively. Each is in L2 by the product norm identity and boundedness of A_1.
This proves the claimed weak domains, not just a formal product formula away
from the nucleus. The P_2 formulas follow by exchange.

Since Phi_Z is an L2 unit product, the integral <Phi_Z,F_sigma> is absolutely
convergent on R6. Fubini in (9) now gives, on all ambient full-spin L2 inputs,

    P_1 P_2 F = P_2 P_1 F,
    (P_1 P_2 F)_sigma = Phi_Z <Phi_Z,F_sigma>.               (11)

In general P_1 and P_2 individually **do not preserve the fermionic subspace**:
particle exchange interchanges these two maps. Their sum and their joint product
do preserve it. The projection norm inequality is accordingly proved in the
ambient space and only then restricted to fermionic vectors.

For any two commuting orthogonal projections P,Q on a Hilbert space, the four
maps PQ, P(I-Q), (I-P)Q and (I-P)(I-Q) give mutually orthogonal components with
sum the identity. Applying P and Q to this decomposition yields the exact identity

    ||PF||^2+||QF||^2
       = ||F||^2+||PQF||^2-||(I-P)(I-Q)F||^2
       <= ||F||^2+||PQF||^2.                               (12)

This is precisely the abstract statement compiled in
CommutingProjectionComparison_v1.lean. It requires no spectral decomposition of
an unbounded tensor-product operator.

For a fermionic F put a_sigma=<Phi_Z,F_sigma>. Since Phi_Z(y,x)=Phi_Z(x,y),
changing the integration variables in (1) gives

    a_(sigma_2,sigma_1)=-a_(sigma_1,sigma_2).

The equal-spin coefficients vanish and the two opposite-spin coefficients are
negatives. Therefore a=c chi, where c=sum_sigma conjugate(chi_sigma)a_sigma
=<G_Z,F>. Equation (11) becomes

    P_1 P_2 F = <G_Z,F> G_Z,
    ||P_1 P_2 F||^2=|<G_Z,F>|^2.                           (13)

Thus the joint projection has rank four in the ambient full spin space and rank
one on the fermionic subspace. It has scalar rank one if spin is absent. No
spin multiplicity has been dropped when asserting (13).

## 4. Combining the kinetic normalization and nonnegative repulsion

Adding (8), using ||A_i F||=||P_i F|| and then (12), gives

    e_1(F)+e_2(F)
       >= -(Z^2/4)||F||^2-(3Z^2/8)(||P_1F||^2+||P_2F||^2)
       >= -(5Z^2/8)||F||^2-(3Z^2/8)||P_1P_2F||^2.          (14)

The sign in the second line uses 3Z^2/8>=0. The repulsive term is nonnegative,
so q_Z>=e_1+e_2. Combining with (13) proves (3), and the one-component version
proves (2). These estimates hold on actual H1 and hence on the actual H2
operator domain. There is no factor of two or four from summing spin states.

In particular all triplet states have <G_Z,F>=0 and satisfy q_Z[F]>=beta_Z||F||^2.
More generally (3) applies to every fermionic vector, even without definite
spin or spatial symmetry. The exceptional vector G_Z is a comparison vector;
it is not being declared an interacting eigenfunction.

## 5. Exact H2 product trial and elementary physical moments

For any alpha>0, repeated elementary integration by parts gives

    integral_0^infinity r^k exp(-t r) dr = k!/t^(k+1)
       (integer k>=0, t>0).                                (15)

The exponential boundary term vanishes at infinity, the k=0 integral starts the
induction, and the origin term vanishes when k>0. Polar integration then gives

    ||phi_alpha||_2^2 = 4alpha^3 integral r^2 exp(-2alpha r) dr = 1,
    integral |phi_alpha(x)|^2/|x| dx = alpha,
    ||grad phi_alpha||_2^2 = alpha^2.                        (16)

The actual H2 membership used above applies with alpha in place of Z. Equivalently
its first derivatives are bounded by alpha phi_alpha and its off-origin Hessian
by a constant times (alpha^2+alpha/|x|)phi_alpha; these are L2. Integration by
parts outside a ball of radius epsilon gives vanishing boundary terms as
epsilon tends to zero (area O(epsilon^2), bounded first derivatives), so these
are the actual weak derivatives without a delta contribution. Tensor products
of the first and second weak derivatives show Phi_alpha in actual H2(R6).
Multiplication by chi preserves that domain and gives a unit fermionic vector.
The nucleus and pair collision intersections require no removal from H2.

For the repulsion integral write r=|x|, s=|y|. With ordinary sphere area measure,
rotation and the substitution t=omega dot eta give, for r,s>0,

    integral_S2 integral_S2 1/|r omega-s eta| d omega d eta
      = 8pi^2 integral_(-1)^1 (r^2+s^2-2rs t)^(-1/2) dt
      = 8pi^2 ((r+s)-|r-s|)/(rs)
      = 16pi^2/max(r,s).                                   (17)

When r=s the endpoint angular singularity is integrable and the same formula
holds by its improper integral; Tonelli licenses all integrations because the
integrand is nonnegative. Sets r=0 or s=0 do not affect the integral. Thus

    J_alpha := integral_R6 |Phi_alpha(x,y)|^2/|x-y| dx dy
      = 16alpha^6 integral_0^infinity integral_0^infinity
          r^2 s^2 exp(-2alpha(r+s))/max(r,s) dr ds
      = 32alpha^6 integral_0^infinity s^2 exp(-2alpha s)
                         [integral_s^infinity r exp(-2alpha r) dr] ds
      = 32alpha^6 integral_0^infinity
          (s^3/(2alpha)+s^2/(4alpha^2)) exp(-4alpha s) ds
      = 32alpha^6 [3!/(2alpha(4alpha)^4)
                            +2!/(4alpha^2(4alpha)^3)]
      = 5alpha/8.                                          (18)

The factor 32 comes from the two ordered radial regions r>=s and s>=r;
the diagonal has two-dimensional radial measure zero. Equations (16)--(18)
give two kinetic contributions alpha^2/2, two nuclear contributions -Zalpha,
and repulsion 5alpha/8. This proves (4) directly on the continuum.

Completing the square gives

    m_Z(alpha) = (alpha-(Z-5/16))^2-(Z-5/16)^2.

For positive alpha the stated minimum is achieved at alpha_*=Z-5/16 when
Z>5/16. The strict inequality in (5) is equivalent to

    96Z^2-160Z+25>0.

Its roots are (20-5sqrt(10))/24 and Z_*. The lower root is below 5/16,
so the positive-alpha minimizing branch gives exactly Z>Z_*. In particular
Z>=3/2 suffices; at Z=3/2 the separator margin is 1/256. At Z=2,
alpha_*=27/16, m_*=-729/256 and d_Z=89/256. These are exact rational examples,
not floating-point spectral measurements.

For comparison, the unoptimized alpha=Z trial has mean -Z^2+5Z/8 and beats
beta_Z only for Z>5/3. The optimized alpha is an auxiliary physical variational
comparison trial. It generally is not a vector of a fixed finite stage of the
original dictionary sum_j exp[-Z 2^j(r+s)] P_sym_(n-2j)(r,s,u). This manuscript
neither changes that dictionary nor claims its approximation theorem for a new
schedule. A branch comparison may use any legitimate physical trial without
altering which vectors the subsequent approximation algorithm is permitted to use.

## 6. Attainment, simple branch and the actual continuum interval implication

Here is the existing rank-one mechanism specialized to these constants. For a
self-adjoint actual operator A, suppose

    beta ||u||^2 <= Re<u,Au>+C |l(u)|^2                     (19)

on D(A), with l a bounded scalar linear functional and C>=0. Every real spectral
point e<beta has actual unit approximate eigenvectors in D(A). Their l-values
have a convergent subsequence because a bounded subset of the finite-dimensional
scalar space has compact closure. Apply (19) to differences and shift A by e.
Cauchy--Schwarz bounds the shifted form of a difference by its norm times its
vanishing residual. The strict coefficient beta-e>0 and the convergent scalar
defect force this subsequence to be norm Cauchy. Completeness and the actual
closed graph give a unit eigenvector at e, rather than a zero weak limit. This
argument is formalized abstractly in RankOneSpectralAttainment_v1.lean.

A strict unit trial puts the actual spectral bottom E below beta. Thus the
preceding argument gives a unit ground vector g. The same rank-one comparison
then implies the full g-orthogonal form bound beta: for w perpendicular to g,
apply (19) to l(w)g-l(g)w, whose l-value vanishes, and use Ag=Eg. Since E<beta,
one first obtains l(g) nonzero, and the exact quadratic expansion gives the
complement bound. This is HardyRankOneComplement_v1.lean. Every distinct
spectral point below beta would also be an eigenvalue and its eigenvector would
be orthogonal to g, contradicting that complement. A ground eigenvector
orthogonal to g is likewise zero; the ground eigenspace is one-dimensional.
The arbitrary phase of its unit generator is retained.

For the full fermionic realization, take A=H_Z, l(F)=<G_Z,F>, beta=beta_Z,
C=C_Z and trial G_(alpha_*). Their hypotheses are precisely (3)--(5).
CoulombRankOneBranch_v1.lean already proves the resulting conditional statement
for the exact current continuum definitions. For the scalar realization use
l(f)=<Phi_Z,f> and (2); this requires the separately declared scalar realization.
The lower bound -Z^2 follows independently by dropping nonnegative repulsion
and applying the one-electron ground lower bound twice.

On the scalar side the attained simple bottom satisfies the reviewed
SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md hypotheses. Its modulus/form argument
returns the nonnegative minimizer to actual H2 by configuration Hardy and the
weak Fourier bridge. Simplicity then fixes its nonnegative unit generator under
spatial rotations and exchange. Multiplication by chi yields a physical unit
fermionic eigenvector with scalar energy. Componentwise scalar lower bounds
and this vector prove equality of the two actual spectral bottoms and their
singlet ground identification. The newer scalar simplicity-from-attainment
paper is a separate route to simplicity, but is not needed to close this
rank-one comparison argument. Strict positivity, when used, comes from the
separate reviewed actual-H2 positivity theorem, not from a pointwise assertion
about the product comparison vector.

The complement also extends from H2 to H1: approximate w in H1 by H2 vectors v_n,
then subtract <g,v_n>g. The actual g lies in H2, and this subtraction preserves
H1 convergence to a ground-orthogonal w. Form continuity gives the same bound.
For the fixed charge range here the actual ground-complement separation is at
least d_Z=beta_Z-m_*>0. This quantitative statement comes from a form comparison,
not from identifying the essential-spectrum or ionization edge.

In particular, if an actual unit fermionic H2 vector v has mean mu, and real
numbers L,U,r satisfy

    L<=mu<=U<beta_Z,
    ||(H_Z-mu)v||^2<=r,

then the already compiled directed Temple implication gives

    L-r/(beta_Z-U) <= inf spec(H_Z) <= U.                    (20)

It uses only v in D(H_Z), not v in D(H_Z^2). Its physical comparison premise is
(3), and attainment and the complement are supplied as above. Equation (20)
is not itself an implementation producing certified moment bounds or accepting
arbitrary numerical data. Exact normalization, means, residuals, directed
rounding and a terminating coefficient procedure retain their separate
formal and computational obligations.

## 7. Evidence, source comparison and unresolved formal work

The formal theorem CommutingProjectionComparison_v1.lean proves the generic
projection inequality and combination constants. Its physical projection and
form hypotheses are constructed here at paper level. The actual physical
hydrogen complement itself likewise remains a reviewed paper proof. Consequently
this manuscript does not turn CoulombRankOneBranch_v1 or its interval consequence
into an unconditional Lean theorem for the atom. Full Theorem T remains unverified.

Primary comparison: Teschl's author-hosted 2009 text, Theorem 10.9 and the radial
factorization in Theorem 10.10, concern the scalar operator -Delta-gamma/r;
substituting gamma=2Z and dividing by two reproduces the ground and complement
constants used here. The relevant theorem text was opened at the author's site.
This is a normalization and applicability check, not a supplied formal proof.
The product and projection arguments above are explicit and make no novelty
claim. Source: [Mathematical Methods in Quantum Mechanics, sections 10.2--10.4](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).

Exact source dependencies read for this version:

| Source relative to this continuation | SHA-256 |
|---|---|
| paper/HYDROGEN_COMPLEMENT_REDUCTION_v2.md | fb3a2d6810347d44a67653f64b5bd41f4c42457843ef1f5191ebdc6eb7255734 |
| paper/HYDROGEN_RADIAL_COMPLEMENT_v1.md | 562fc81c7dff2056b20e8d496ef62f375a3550652222bb02aa17644d63b1e585 |
| audits/SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md | 605b1a0261a74f00d4181c193ffe8515b6a5ee8f4e41eeefcf6b3c02e59fd841 |
| audits/COULOMB_NONNEGATIVE_STRICT_POSITIVITY_v1.md | fb57d21629cf77c5c7a4194921b7fc2e1a9c1172f15bc909b0836474e82d3a37 |
| lean/CommutingProjectionComparison_v1.lean | 6421a7494aa6ad7a4f0c4547e967feec9ec442eeaa0720577bb635c2f6fec5e2 |
| lean/RankOneSpectralAttainment_v1.lean | 53080e1f9b3eb265642fb39114a954ef158e11b1be529ab5169abe5475a01ca9 |
| lean/HardyRankOneComplement_v1.lean | 98c2c98674055f4015e7e9c51be7d08a6b5366fa90602137bd39d7c068a44efc |
| lean/HardyRankOneTemple_v1.lean | 9ae612906ec8d347545d8cc77d3530286125aae2b5557294f04922012c3e50dc |
| lean/CoulombRankOneBranch_v1.lean | 59cab9c13de43673ce2a0c0069eb1e7659e0c399cbf9073663f73df7643c3ad5 |
| lean/CoulombRankOneCertificate_v1.lean | f6a7648c954db74257a6a9a4e27e64b5f08ea7f7a4e5a7287ef9bdd3a21d25b8 |

The scalar simplicity-from-attainment draft was also read at SHA-256
53bad2e68b8c95e146a0e93803e55209ff1f88fc68227abe41632a56323c66a8;
it is not a required dependency for the rank-one route in this manuscript.

Next formal obligations are (i) the actual one-electron complement proof,
(ii) slice and partial-contraction maps with their weak derivatives,
(iii) the ambient projections and exact fermionic joint projection identity,
(iv) physical angular/radial integral identities and the normalized H2 trial,
and (v) instantiation of the compiled branch and certificate theorems. This is
substantive mathematical completion at paper level of these bridges, while
preserving their precise formalization boundary.

Frozen baseline: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag
theorem-t-proof-freeze-2026-09-09. The frozen physical target
THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RWA_THEOREM.md has SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09.
New continuation files only; no frozen or sealed successful artifact was changed.
This version requires independent exact-source review before being labelled reviewed.
