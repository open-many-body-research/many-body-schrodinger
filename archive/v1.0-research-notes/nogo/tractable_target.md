> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# A tractable continuum target for the next session

This is independent mathematical planning, without a new literature search. **No polynomial-time continuum solver is proved in this document.** The target below is a conjectured restricted-class result, together with a precise sufficient theorem and its elementary proof. It is not an exhaustive classification under option (c), and its failure would not establish a complexity obstruction under option (d).

## 1. Recommended physical class

Fix positive rational constants `rmin < rmax`, `mu_gap`, and `mu_ion`, and a fixed integer `Zmax >= 1`. Put `mu=min(mu_gap,mu_ion)`. The varying input is

* a nuclear count `M∈{1,2}` and positive integer charges `1 <= ZA <= Zmax`;
* for `M=2`, a rational internuclear separation `rmin <= R <= rmax`;
* a requested number of accuracy bits `b >= 1`.

For `M=1`, the nucleus is at the origin. For `M=2`, the nuclei are at `(0,0,−R/2)` and `(0,0,R/2)`. There are exactly two electrons. Use the full antisymmetric Hilbert space

    H_f = wedge² L²(R³ × {up,down}; C),

the Coulomb Hamiltonian specified by these nuclei, operator domain `H² ∩ H_f`, and form domain `Q = H¹ ∩ H_f`. All spatial integrals extend over unbounded Euclidean space. No basis, box, pseudopotential, or cutoff belongs to the definition of this physical Hamiltonian.

Let `E0=inf spectrum(H)`. The explicit **ground-state and ionization promises** are

    dim ker(H−E0)=1,
    spectrum(H) \ {E0} ⊆ [E0+mu_gap, infinity),
    inf essential_spectrum(H) − E0 >= mu_ion.

The last condition explicitly controls ionization; the middle condition controls separation from other electronic states. The class consists exactly of these input Hamiltonians satisfying that predicate. A gap is a promise here, not an unverified numerical diagnostic. A theorem claiming that all separations in a specified interval satisfy the promises must prove that separately. For a nonvacuous application, choose the constants and certify at least one member, preferably an interval of separations. The gap constants can instead be input with `mu >= 1/poly(L)`, but the first target should keep them fixed.

This family contains ordinary two-electron diatomics, including the portion of an H₂ potential curve meeting the gap promise. A fixed bounded interval can include equilibrium and stretched geometries. It excludes an unbounded dissociation limit; choosing a large `rmax` may force a very small gap constant and large hidden costs. Bounded electron number makes the configuration-space dimension fixed. Positive bounded charges and noncolliding nuclei constrain the geometry. **None of these facts, even combined with the gap, by themselves gives an efficient algorithm.**

The spinless symmetric spatial formulation with a fixed singlet factor is equivalent only after proving that the physical ground state lies in that sector. That proof must be supplied, rather than achieved by redefining the physical problem. The full fermionic formulation above avoids concealing the issue in the class definition.

## 2. Desired algorithm theorem — CONJECTURED

Write `L` for the binary input length of the nuclear data `(M,{ZA},R)` with the separation omitted when `M=1`. There exist a deterministic Turing machine `A` and constants `C,k`, depending only on the fixed class constants, such that on every promised input and every `b`, in at most `C (L+b)^k` bit operations it outputs:

1. rational numbers `ell <= u` with `u−ell <= 2^(-b)` and `ell <= E0 <= u`;
2. a finite explicitly evaluable description of a normalized trial state `w_b ∈ Q` for which

       inf_{|z|=1} ||w_b − z psi0||_L² <= 2^(-b),

   where `psi0` is the normalized ground state;
3. a checkable certificate whose stated soundness includes the original continuum operator and all numerical error sources.

The output state can be a polynomial-length list of rational coefficients in an algorithmically specified basis, with normalization expressed using the square root of its Gram quadratic form. A finite description does not require pretending that all exact normalization coefficients are rational.

State approximation gives a precise observable interface: for every bounded operator `O` with `||O|| <= 1`, expectation values differ by at most `2^(1−b)`. To **compute** such an expectation, the operator must also have an explicit representation allowing its trial-space matrix elements to be certified in polynomial bit complexity. Physically useful first targets are bounded Gaussian probes of the one-electron density with rational centers and exponents in fixed compact ranges. Arbitrary unspecified observables are not an input model. Kinetic energy, Coulomb energies, positions, and forces are unbounded and need additional graph/form/moment error estimates; L² accuracy alone does not certify them.

This theorem would settle a meaningful restricted case related to option (b). It would **not** settle general `(N,M)` electronic structure or characterize exactly which classes admit (b).

## 3. A sufficient constructive approximation theorem

The real research burden is the following statement. It should be proved with explicit constants, not introduced as the conclusion of a numerical fitting exercise.

**Uniform constructive weighted-analytic `hp` approximation and enclosure theorem (target).** For the class in §1, an algorithm constructs, from the nuclear input `x` and a resolution index `p>=1`, a finite-dimensional conforming space `V_(x,p) ⊂ Q` and a basis with all of these properties:

**A. Uniform continuum approximation.** There are known positive constants `C0,c`, with an effective procedure for bounding them, such that for every normalized ground state,

    inf_{v ∈ V_(x,p)} ||psi0−v||_H¹ <= C0 exp(−c p).

For the fixed physical class the constants are uniform in `R`. A broader varying class may allow `log(C0)` and `1/c` to be bounded by explicit polynomials in `L`; that still permits polynomial cost in `L+b`. Mere existence of unspecified positive constants is insufficient for a certified algorithm.

**B. Polynomial representation size.** The space and basis can be constructed in `poly(L,p)` bit operations, and `dim V_(x,p) <= poly(L,p)`. The exponent is permitted to depend on the fixed electron count. No claim is made uniform in growing configuration-space dimension.

**C. Effective conditioning and integration.** Gram, Hamiltonian, and required observable matrices can be enclosed to any prescribed norm error `2^(-s)` in `poly(L,p,s)` bit operations. Basis normalization/conditioning must be controlled so that at most `poly(L,p,s)` precision bits suffice. A claim of exponential approximation together with exponentially large *required precision bits* would not establish the desired algorithm.

**D. Validated finite linear algebra.** For any requested integer `s>=1`, a routine using `poly(L,p,s)` bit operations encloses the exact lowest generalized eigenvalue `a_p` in an interval of width at most `2^(-s)` and returns an explicitly described normalized vector `w∈V_(x,p)` with the certified near-optimality bound `q_H[w] <= a_p + 2^(-s)`. Both certificates account for errors in the Gram and Hamiltonian matrices. A bound on an arbitrary high-energy trial vector would not suffice for the state conclusion below. Standard finite algebra is a manageable component; its input precision and conditioning assumptions remain explicit.

The natural analytic route toward A and B is constructive weighted analytic regularity near the electron–nucleus/electron–electron collision sets, explicit treatment of intersections and possible logarithmic coalescence terms, geometric refinement or enriched approximation, and quantitative decay outside a growing computational region. A global analytic wavefunction cannot be assumed: Coulomb cusps are present. A bare assertion that a geometric `hp` mesh has exponential convergence is not enough; its approximation class, local weights, singular strata, dimension growth, constants, and uniformity in the molecular geometry must be proved.

For C, certified integration across Coulomb singular sets must itself have the required bit complexity. A high-order method with unanalysed quadrature, heuristic basis extrapolation, or numerically inferred asymptotic convergence does not satisfy C.

**Important domain issue:** ordinary conforming `C⁰` finite elements lie in `H¹`, but generally not in the operator domain `H²`. Their distributional Laplacians have interface terms. Consequently one cannot apply an L² residual formula `||(H−a)v||₂`, or an operator `QHP` bound, without a domain argument. Use a form-based certificate, prove enough regularity of the chosen basis, or use smooth/`H²` trial spaces.

## 4. Why A–D suffice: a complete elementary bridge proof

The result in this section is a **human proof of a conditional implication**. Its hypotheses include the unproved approximation and computational assertions in §3.

First obtain explicit uniform constants `K,B` satisfying

    |q_H[f]| <= K ||f||_H¹²,                 f ∈ Q,
    −B <= E0 <= 0.

The form constant follows explicitly from Hardy's inequality. Put `Z=sum_A ZA`, `F=||f||₂`, `gi=||gradient_i f||₂`, and `G²=g1²+g2²`. Slicing Hardy's inequality in one electron coordinate gives

    ∫ |f|²/|ri−A| <= 2 gi F <= gi²+F².

Consequently the magnitude of the total nuclear attraction is at most `Z(G²+2F²)`. The two sliced Hardy bounds for the pair interaction are `2g1 F` and `2g2 F`; averaging gives

    ∫ |f|²/|r1−r2| <= F(g1+g2) <= G²/2+F².

The kinetic form is `G²/2`. The triangle inequality therefore gives the absolute form bound

    |q_H[f]| <= (Z+1)G²+(2Z+1)F²
             <= (2Z+1)||f||_H¹².

For the energy lower bound, use the stronger hydrogen square-completion argument in [physical_scales.md](nogo/physical_scales.md), §2: write each one-electron operator as the convex combination, with weights `ZA/Z`, of hydrogenic operators with charge `Z` at the different centers. Each is bounded below by `−Z²/2`. Summing the two electron bounds and retaining nonnegative repulsion yields `E0>=−Z²`. The upper bound `E0<=0` follows by dilating a normalized compactly supported fermionic trial state and discarding the nonpositive nuclear attractions. Thus valid explicit constants are

    K = 2Z + 1,       B = Z².

These estimates are uniform in the nuclear positions. In the proposed family, replace `Z` by `2 Zmax` if a common constant is desired.

Let `psi0` be normalized and let `v∈V_(x,p)` satisfy `||v−psi0||_H¹<=eta`, where `eta=C0 exp(−cp)<=1/2`. Put `e=v−psi0`. The weak eigenvalue equation cancels the cross terms:

    q_H[v] − E0 ||v||₂² = q_H[e] − E0 ||e||₂².

Also `||v||₂>=1−eta>=1/2`. Therefore its normalized Rayleigh quotient is at most

    E0 + 4(K+B) eta².

If `a_p` is the exact minimum Rayleigh quotient in `V_(x,p)`, the variational principle yields

    a_p − D_p <= E0 <= a_p,
    D_p = 4(K+B) C0² exp(−2cp).                 (*).

This is already a **continuum lower certificate**. It does not require separately computing a complementary-space operator norm: the globally valid approximation theorem A supplies the missing continuum control. If A only says convergence without an effective rate, (*) does not yield an executable certificate.

Choose `p=O(L+b)` in the fixed-constant case, or the explicit polynomial prescribed by the allowed `L`-dependence of `C0,c`, so that `D_p` is smaller than a fixed fraction of `2^(-b)`. Use C and D to enclose `a_p` by `[a_minus,a_plus]` with width below the remaining budget. Then

    [a_minus−D_p, a_plus]

is a certified interval for `E0` of the required width. Every computed exponential/rational bound and linear-algebra error must be rounded outward. B–D imply polynomial bit cost, since `p` and requested matrix precision are polynomial in `L+b`.

To certify the state as well, perform the energy approximation more accurately. Let `w` be the returned normalized trial state with

    q_H[w]−E0 <= delta.

Write `w=a psi0+w_perp`. The spectral gap gives

    ||w_perp||₂² <= delta/mu.

Choosing the phase of `psi0` so that its overlap with `w` is nonnegative gives

    ||w−z psi0||₂² = 2−2|a| <= 2(1−|a|²)
                      <= 2delta/mu.

It suffices to make `delta <= mu·2^(-2b−1)`. This requires only `O(b+log(1/mu))` energy-accuracy bits. Approximate finite eigenvectors can be certified through their actual Rayleigh quotient; a spectral-gap lower bound for the finite Ritz matrix also follows once `D_p<mu/2`, because the second Ritz value is at least the second continuum spectral level. No assumption that a local optimizer finds the global minimum is needed: the finite matrix problem is solved by certified linear algebra.

Finally, for `||O||<=1`, expand the difference of expectations as

    <w,Ow>−<psi0,Opsi0>
      = <w−z psi0,Ow> + <z psi0,O(w−z psi0)>.

Cauchy–Schwarz bounds its absolute value by `2||w−z psi0||₂`. Certified matrix-element integration adds its separately allocated tolerance. This proves the stated bounded-observable interface.

## 5. If the approximation proof uses complementary-space bounds instead

An alternative is to construct exact trial projections `P_p`, with `Q_p=I−P_p`, and prove a computable lower bound for the omitted continuum sector plus controlled coupling. With operator-domain trial states, sufficient data are

    a_p = min spectrum(P_p H P_p),
    q_H[y] >= d_p ||y||²   for y∈Q_p Q,
    ||Q_p H P_p|| <= b_p.

For any desired `eta>0`, the condition

    d_p >= a_p − eta + b_p²/eta

implies `a_p−eta <= E0 <= a_p` by completing the square in the two orthogonal components. This is a useful explicit certificate target, but it can be too stringent or difficult to prove for a particular mesh. It is not automatically true for a small-overlap Gaussian basis. For ordinary form-domain finite elements, use a rigorously justified form version instead of pretending `HP_p` is an L² operator.

The next session should select **one** legitimate continuum lower-bound route: effective approximation theorem (*) or a complementary-space certificate. Establishing both is unnecessary. Proving neither leaves the original finite-basis gap unresolved.

## 6. Scope decisions and work for the next session

Start with the two-electron diatomic class, or narrow further to `Z1=Z2=1` and an explicit rational interval of separations. A helium-like `N=2,M=1` class eliminates nuclear-geometry issues and is a useful intermediate test, but bounded integer charges then leave only finitely many Hamiltonians; it is weaker evidence for a uniform structural tractability theorem. Rationally varying effective charges create a nontrivial family, but are not literal integer-charge nuclei and must be labeled accordingly.

The next session's concrete theorem should be A–D with an explicit construction, followed by the bridge above and a verified implementation. A sensible staged target is first to prove A with explicit constants and the dimension bound for one fixed two-electron Coulomb Hamiltonian, then establish uniformity over the molecular geometry and verified matrix integration. If those analytic results cannot be established, report the desired algorithm theorem as **CONJECTURED**, retaining the conditional bridge as the proved result. Do not relabel it a proved class satisfying (b).

After that, a fixed `N<=Nstar`, fixed `M<=Mstar`, bounded-charge compact noncollision family is a natural extension. Allowing `M` to grow adds singular strata, geometry complexity, and uniform-constant obligations. Allowing `N` to grow removes the fixed-dimension benefit; an exponent depending on `N` is not a polynomial bound in `N`.

The most important precise open theorem here is: **Do A–D hold uniformly for the promised unbounded-space two-electron Coulomb family with one or two nuclei in §1, with a fully explicit polynomial bit bound?** A positive answer would turn practically accurate basis convergence into a certified continuum algorithm for a meaningful restricted family. Neither a gap promise nor an entanglement bound alone answers this question.
