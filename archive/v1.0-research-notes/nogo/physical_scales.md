> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Physical energy scales and the limits of scalar no-go arguments

**Status: PROVEN (paper proof only).** This file proves the claims it uses at the level of quadratic forms, using the continuum operator and domain defined in [research/analytic.md](research/analytic.md). It does not assert a Lean formalization. No Gaussian integrals were rerun for this argument.

## 1. Model and notation

Let N,M≥1 be integers; let Z_A>0 be finite charges and R_A∈R³ fixed nuclear locations. Write Z_tot=Σ_A Z_A and let H_N be the electronic Coulomb Hamiltonian on antisymmetric L²((R³×{↑,↓})^N), with spatial H² operator domain and H¹ quadratic-form domain. Nuclear repulsion is **not** included, matching the original displayed Hamiltonian. Coincident nuclear locations do not invalidate the electronic form or the estimates below; they would invalidate a finite nuclear-repulsion constant if one were added.

Write E_N=inf σ(H_N), whether or not it is an eigenvalue, and set E_0=0. Define

    C_N = N Z_tot²/2.

We distinguish three unrelated quantities:

* μ>0: a promised **ionization margin**, E_{N−1}−E_N≥μ;
* g=B−A>0: a **decision-promise gap** between common YES and NO energy thresholds;
* η≥0: an allowed **continuum-transfer error** of a finite variational subspace.

A gap above a ground eigenspace is a fourth, different quantity. No such excited-state gap is assumed here. The bounds below use μ only through the stated ionization inequality.

## 2. A universal geometry-independent energy bracket

**Theorem 1.** For every instance just defined,

    −N Z_tot²/2 ≤ E_N ≤ 0.                         (1)

**Proof of the lower bound.** For Q>0 and any center R, the hydrogen square-completion identity is

    ½∫|∇f|² − Q∫|f|²/|r−R| + (Q²/2)∫|f|²
       =½∫|∇f+Q[(r−R)/|r−R|]f|² ≥0.             (2)

First take smooth compactly supported f. Expanding the square gives a cross term Q/2 times the integral of [(r−R)/|r−R|]·∇|f|². Its integration by parts equals −Q∫|f|²/|r−R|, since the vector field has divergence 2/|r−R| and no delta mass at R: its flux through a sphere of radius δ is 4πδ²→0. Hardy's inequality makes the Coulomb integral continuous under H¹ convergence, extending (2) to the full form domain. Finite spin sums preserve the identity.

For one electron, write the exact form identity

    −½Δ−Σ_A Z_A/|r−R_A|
      =Σ_A (Z_A/Z_tot)[−½Δ−Z_tot/|r−R_A|].         (3)

The weights are positive and sum to one. By (2), each operator in brackets is bounded below by −Z_tot²/2. Thus the one-electron form in (3) is bounded below by that same number. Apply the inequality to each electron coordinate, with all other spatial and spin coordinates held fixed, and integrate the remaining variables. Each of the N terms contributes at least −Z_tot²/2 times the total squared norm. Electron repulsion is nonnegative, so for every normalized form-domain ψ,

    q_N[ψ]≥−N Z_tot²/2.

Take the variational infimum. The argument does not use particle statistics, so restriction to the fermionic subspace is valid.

**Proof of the upper bound.** Choose a normalized smooth compactly supported antisymmetric N-electron spinor ψ. Such functions exist: take a Slater determinant of N smooth spatial bumps with mutually disjoint supports and a fixed spin. Put

    ψ_L(r₁,s₁,…,r_N,s_N)
      =L^(−3N/2)ψ(r₁/L,s₁,…,r_N/L,s_N),  L>0.

It remains normalized and antisymmetric. Its kinetic form equals T[ψ]/L² and its repulsive Coulomb form equals W[ψ]/L. The finitely many attractive nuclear form terms are finite and nonpositive for every L. Hence

    E_N≤q_N[ψ_L]≤T[ψ]/L²+W[ψ]/L.

Let L→∞ to obtain E_N≤0. This argument does not assume a ground eigenvector or any separated-atom numerical energy. ∎

**Corollary 1.1 (with an ionization margin).** If E_{N−1}−E_N≥μ>0, then

    −C_N≤E_N≤−μ.                                  (4)

Indeed E_{N−1}≤0 by Theorem 1, or by the convention E_0=0 when N=1. Thus E_N≤E_{N−1}−μ≤−μ. In particular the assumptions require μ≤C_N. By the HVZ background theorem stated in research/analytic.md, this positive ionization margin also implies that E_N is a discrete ground eigenvalue. The numerical inequalities in this file do not require that spectral consequence.

An optional stronger consistency bound on the margin is μ≤Z_tot²/2. To see it, decompose H_N into H_{N−1} acting on all but one electron, that last electron's one-body Hamiltonian, and its nonnegative pair repulsions. Antisymmetric slices of a fermionic N-electron vector are antisymmetric in the remaining N−1 variables. The variational lower bound for H_{N−1} and (3) therefore give E_N≥E_{N−1}−Z_tot²/2.

## 3. What a finite-subspace transfer theorem actually constrains

Let P project onto a nonzero finite-dimensional subspace of the fermionic form domain, let a be the minimum of q_N on its unit sphere, and suppose a **proved** transfer estimate gives

    0≤a−E_N≤η.                                    (5)

The first inequality is automatic from the variational principle. The second is additional information: an accurately integrated projected Hamiltonian does not establish it.

**Theorem 2.** Under (4) and (5),

    −C_N≤a≤−μ+η.                                  (6)

**Proof.** The lower bound follows from a≥E_N≥−C_N. The upper bound follows from a≤E_N+η≤−μ+η. ∎

In particular, every allowed transfer budget must satisfy

    η≥a+μ                                          (7)

whenever the right side is positive. If the task additionally demands η≤θg for a specified θ≥0 and promise gap g>0, a necessary condition is

    a+μ≤θg.                                        (8)

Thus an instance with a+μ>θg cannot satisfy that **specified accuracy budget**. A positive projected energy is not by itself a theorem that no transfer estimate of any size exists. If θg<μ, then (6) does force a<0; if θg≥μ, even a small positive a is consistent with these scalar inequalities.

If the symbol “gap” means an excited-state gap rather than a decision-promise gap, the substitution η≤θΔ_excited still gives a≤−μ+θΔ_excited, but the common-threshold bounds in §4 say nothing about Δ_excited. Conflating these gaps would change the theorem.

## 4. Common physical thresholds with actual witnesses

Consider a family F with uniform bounds C_N≤C_max and ionization margins at least μ_min>0. Every energy in the family lies in

    [−C_max,−μ_min].                               (9)

Choose a **single common pair of thresholds** A<B for this family. Define YES to mean E_N≤A, and NO to mean E_N≥B. Suppose there is at least one YES instance and at least one NO instance in F.

**Theorem 3.** These hypotheses imply

    A≥−C_max,  B≤−μ_min,
    0<g:=B−A≤C_max−μ_min.                          (10)

**Proof.** For a YES witness, −C_max≤E_Y≤A, so A≥−C_max. For a NO witness, B≤E_N≤−μ_min, so B≤−μ_min. Subtract the threshold bounds and use A<B. ∎

Combining Theorems 2 and 3 with an imposed budget η≤θg gives the necessary bound

    −C_N≤a≤−μ+θ(C_max−μ_min).                      (11)

This is a condition on a subspace alleged to approximate the physical ground energy within the specified promise-gap budget. It is not a bound on arbitrary trial-state energies, which can be arbitrarily high.

### Why an arbitrary enclosing window is different

From “all energies lie in [L,U]” one cannot deduce L≥−C_max or U≤−μ_min. For example, energies lying in [−4,−1] also lie in [−10¹⁰⁰,10¹⁰⁰]. There is no contradiction: enclosure only requires the endpoints to lie outside the values. Theorem 3 uses actual YES and NO witnesses with the **opposite inequalities** relative to A and B.

The thresholds must also genuinely be common. If each instance has its own thresholds, merely having YES and NO instances somewhere in the family does not give (10) for every threshold pair. For example, an energy E=−1 is a YES instance under A=100,B=10¹⁰⁰ and a NO instance under A=−10¹⁰⁰,B=−100. Both pairs have enormous gaps, but no single pair has both witnesses. An affine reduction with input-dependent shifts needs a separate argument before common-threshold reasoning can be applied.

## 5. Consequence for a bounded-charge family

Let n≥1 be an input-size parameter. Suppose fixed exponents p,q≥0 and a fixed charge bound Z_max>0 satisfy

    N≤n^p,  M≤n^q,  0<Z_A≤Z_max.

Then Z_tot≤M Z_max and

    C_N=N Z_tot²/2≤(Z_max²/2)n^(p+2q)=:C_max(n).   (12)

For a family with a common positive ionization-margin lower bound μ_min(n), every nontrivial common physical energy promise therefore has

    g≤(Z_max²/2)n^(p+2q)−μ_min(n).                 (13)

The nuclear coordinates do not enter this coarse bound. A fine coordinate grid, close nuclear approaches, large coordinate numerators, and large numerical energies of specially chosen trial functions do not enlarge the electronic ground-energy bracket (1), provided the charges and particle counts remain as stated. If nuclear repulsion is added to the Hamiltonian, it adds a geometry-dependent scalar to both bounds and the statement must be modified accordingly.

A coordinate grid alone establishes neither an efficient algorithm nor hardness. Even a finite polynomial-bit grid can permit exponentially many configurations; conversely, a polynomial range of possible energies does not imply that selecting the correct small energy interval is computationally easy. This file establishes an energy-scale constraint, not a classification of computational complexity.

### An affine scale bound, with all additional hypotheses exposed

Suppose a source promise has common thresholds u<v, Δ=v−u>0. Suppose a reduction uses a positive scale ρ and a common shift c, a finite-space eigenvalue a obeys

    |a−(c+ρe_source)|≤δ,

and continuum transfer obeys (5). These imply the valid physical thresholds

    A=c+ρu+δ,
    B=c+ρv−δ−η,
    g=ρΔ−2δ−η.                                   (14)

Here the asymmetry in η is deliberate: the variational inequality E≤a strengthens the YES direction, while E≥a−η is needed for NO. Assume both source labels have image witnesses in the physical family, and the total reduction error obeys the **non-collapse condition**

    2δ+η≤θρΔ,  0≤θ<1.

Then g≥(1−θ)ρΔ>0, and Theorem 3 yields

    ρ≤(C_max−μ_min)/[(1−θ)Δ].                     (15)

For the bounded-charge family and an inverse-polynomial Δ, this upper bound on ρ is polynomial in n. It does not apply merely because a large constant was subtracted from a projected matrix. The assumptions of a correct continuum transfer, common physical thresholds, both witnesses, and a non-collapsed error budget are essential. Input-dependent shifts cannot silently be treated as a common c.

## 6. Counterexamples to stronger scalar no-go claims

**“No transfer error η can work.”** This is false for any fixed finite variational minimum a. By (1), E_N≥−C_N, so

    0≤a−E_N≤a+C_N.

Since a≥−C_N, the choice η=a+C_N is a nonnegative, valid coarse bound. It may be useless for a computational reduction, but it exists. A valid no-go statement must demand a specified smaller error, such as η≤θg, and prove that this demand conflicts with (7).

For an elementary illustration, let H=diag(−1,100) and let P select the second coordinate. Then E=−1 and a=100. An error budget η<101 fails, while η=101 succeeds exactly. The positive value a=100 is an obstruction to a unit-accuracy claim, not to every conceivable transfer statement. This illustration is finite-dimensional; Theorems 1–3 are the actual Coulomb assertions.

**“A polynomial physical energy range forbids QMA hardness.”** This does not follow. The range constrains the maximum useful common promise gap, not the resources required to distinguish energy values separated by an inverse polynomial. No class separation is proved in this file.

**“A huge shifted finite-basis embedding is automatically a continuum obstruction for every construction.”** This also does not follow. What is ruled out is a specific embedding/transfer package whose projected minimum violates (6) for its claimed η. Another basis, another set of point nuclei, or a different quantitatively justified transfer may behave differently.

## 7. Relation to the existing dimer artifacts

For the selected two-electron/two-unit-charge-nucleus dimer, C_N=4, independently of its extreme Gaussian exponents and core separation. The earlier paper proof in [gaussian/integrals_theory.md](gaussian/integrals_theory.md) gives −4≤E_cont≤0; its projected finite minimum is a different quantity and retains the large positive scalar shift. Any certified inequality a>η already contradicts 0≤a−E_cont≤η. If a positive ionization margin μ is separately supplied, the stronger necessary inequality is a+μ≤η.

The Gaussian integral certificate can establish a bound on a and finite-matrix errors. It cannot by itself establish the complementary-space transfer premise (5). Conversely, the scalar contradiction does not mean the certificate's finite-matrix arithmetic is wrong. These are different mathematical assertions.

The historical hydrogen, Kato-Rellich and HVZ references, their verification status, and the complete domain definitions are recorded in [research/analytic.md](research/analytic.md). No new literature claims are introduced here.
