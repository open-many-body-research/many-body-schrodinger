> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A gap-free continuum enclosure reduction for finite atoms

Date: 2026-09-09. New work, not a modification of the frozen proof. Status: **paper derivation of the continuum bounds and conditional algorithm specification**. No Lean proof, built implementation of `BoxEnclose`, or new numerical energy enclosure is claimed. The eventual end-to-end executable theorem remains conditional on implementing and verifying the bounded-box routine specified below. The proof of the continuum reduction is independent of RWA, spectral gaps, eigenstate existence, and unknown decay constants.

Use N for electron count; p for precision. Definitions, provenance, complexity scope and primary-literature limitations are in `ARBITRARY_N_SCOPE_v1.md`. The baseline frozen source is `TWO_ELECTRON_THEOREM.md`, SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.

## 1. Actual Hamiltonian and elementary bounds

Write T[ψ]=(1/2)Σ_i||∇_iψ||², V for the full uncut Coulomb multiplication operator, q=T+V, and E_N=inf q on normalized H¹ fermionic spin-space states. This agrees with the bottom of the actual self-adjoint operator on `H² ∩ H_N`.

For a three-dimensional variable, Hardy gives `||f/r||₂≤2||∇f||₂`. Slicing in spectator variables and spin gives the nuclear estimates. For a pair, use the orthogonal coordinates y=(x_i−x_j)/√2 and t=(x_i+x_j)/√2 to obtain

\[
\|\psi/|x_i-x_j|\|_2^2
\le2\bigl(\|\nabla_i\psi\|_2^2+\|\nabla_j\psi\|_2^2\bigr).
\tag{1}
\]

Triangle and Cauchy–Schwarz therefore give

\[
\|V\psi\|_2\le \sqrt N(2Z+N-1)\|\nabla\psi\|_2.
\tag{2}
\]

Fourier interpolation makes this an infinitesimal `−Δ` bound on H². Kato–Rellich supplies self-adjointness on H² and equivalence with the graph norm. The finite antisymmetrizing projection is bounded on H² and commutes with T and V, so the fermionic restriction is self-adjoint on the displayed domain. This is a use of a stated classical functional-analytic theorem, not a hidden Coulomb axiom and not a Lean formalization.

For compactly supported smooth f in three dimensions, integration by parts gives

\[
0\le\|\nabla f+\alpha(x/|x|)f\|^2
=\|\nabla f\|^2+\alpha^2\|f\|^2
-2\alpha\int |f|^2/|x|.
\tag{3}
\]

Density and Hardy extend this to H¹. Take α=Z and drop the positive electron repulsion to get

\[
q[\psi]\ge-NZ^2\|\psi\|^2/2.
\tag{4}
\]

Taking α=2Z in (3) similarly yields

\[
q[\psi]\ge\tfrac12 T[\psi]-NZ^2\|\psi\|^2.
\tag{5}
\]

Both apply to Dirichlet states extended by zero from a box. Smooth fermionic compact-support states form a form core: approximate in H¹ by smooth compact support and apply the antisymmetrizer. Hardy makes all potential forms continuous under H¹ approximation.

Also E_N≤E_(N−1) for N≥1, with E_0=0. To see this without assuming any ground state exists, choose a normalized compact-support (N−1)-electron form-core vector close to its energy infimum, add a normalized one-electron bump with support far away from that fixed support, and antisymmetrize. The disjoint one-particle spatial supports make the antisymmetrized product normalized after the usual wedge normalization. The new bump's kinetic energy tends to zero under dilation; nuclear and cross-electron expectations tend to zero under separation. The internal energy is unchanged. Sending the approximation error to zero proves monotonicity. Thus

\[
-NZ^2/2\le E_N\le E_{N-1}\le0.
\tag{6}
\]

The construction includes spin and does not substitute bosonic energies.

## 2. Fermionic localization and a two-sided recursion

For R≥1, define Ω_R=(-2R,2R)^3 and let λ_N(R) be the **fermionic Dirichlet** ground energy on Ω_R^N, with form domain `H¹₀(Ω_R^N; C^(2^N)) ∩ H_N`. This is a bounded-domain form, not the definition of the full-space energy.

Let θ(t)=0 for t≤1, θ(t)=π(t−1)/2 for 1<t<2, and θ(t)=π/2 for t≥2. Put

\[
\chi_i=\cos\theta(|x_i|_\infty/R),\qquad
\eta_i=\sin\theta(|x_i|_\infty/R),
\]

and for each subset A⊆{1,…,N} define

\[
\Phi_A=\prod_{i\in A}\eta_i\prod_{i\notin A}\chi_i.
\]

These are Lipschitz multipliers, Σ_A Φ_A²=1, and direct product differentiation gives almost everywhere

\[
\sum_A |\nabla\Phi_A|^2
=\sum_i(|\nabla\chi_i|^2+|\nabla\eta_i|^2)
\le\frac{N\pi^2}{4R^2}.
\tag{7}
\]

Expanding the weak gradients and canceling cross terms proves the IMS identity

\[
q[\psi]=\sum_A q[\Phi_A\psi]
-\tfrac12\int\sum_A|\nabla\Phi_A|^2|\psi|^2.
\tag{8}
\]

This identity is evaluated on the full componentwise form, since an individual Φ_Aψ need not remain antisymmetric under permutations mixing A and its complement. This issue is essential.

For A=∅, the multiplier is symmetric in all electron labels and has zero trace outside Ω_R^N, so the localized state is fully fermionic and its energy is at least λ_N(R) times its norm squared.

For A≠∅, let k=N−|A|. The multiplier preserves antisymmetry under all permutations **within the k interior labels**. On its support each exterior electron satisfies |x_i|≥|x_i|∞≥R. Drop all exterior kinetic energy and every repulsion involving an exterior electron. The exterior nuclear energy is at least −|A|Z/R. Slice in the exterior variables/spins; the remaining k-particle function is fermionic. Hence

\[
q[\Phi_A\psi]\ge
\left(E_k-|A|Z/R\right)\|\Phi_A\psi\|^2
\ge\left(E_{N-1}-NZ/R\right)\|\Phi_A\psi\|^2,
\tag{9}
\]

where monotonicity covers k=0 as well. Combining (7)–(9) with the variational upper bounds proves the main continuum theorem:

\[
\boxed{
\min\{\lambda_N(R),E_{N-1}-NZ/R\}-\frac{N\pi^2}{8R^2}
\le E_N\le
\min\{\lambda_N(R),E_{N-1}\}.}
\tag{10}
\]

This is an explicit proof of the lower bound, including its fermionic cluster restriction. No HVZ theorem, binding condition, excited-level separator or tail-rate assumption is used.

If rational enclosures [a,b] for λ_N(R) and [c,d] for E_(N−1) both have width≤ε, then (using π²<10)

\[
\left[\min(a,c-NZ/R)-\frac{5N}{4R^2},\ \min(b,d)\right]
\tag{11}
\]

encloses E_N and has width at most `ε+NZ/R+5N/(4R²)`. The width estimate follows from monotonicity and the 1-Lipschitz property of min in the maximum norm, together with `min(a,c)−min(a,c−t)≤t` for t≥0.

## 3. Removing Coulomb singularities with an explicit continuum error

Let `v_M(r)=min(1/r,M)` with value M at r=0, M>0. Define q_M on the same Dirichlet form domain by clipping each nuclear and electron-pair inverse distance at the same M; denote its minimum by λ_M. This is an auxiliary computational form. The unclipped λ_N(R) remains the target and is enclosed quantitatively below.

The pointwise inequality

\[
0\le(1/r-M)_+\le\frac1{4Mr^2}
\tag{12}
\]

follows by maximizing r−Mr². Combining it with Hardy and (1) gives, for every Dirichlet form state,

\[
|q[\psi]-q_M[\psi]|\le\delta_M T[\psi],\qquad
\delta_M=\frac{2Z+N-1}{M}.
\tag{13}
\]

For clarity: nuclear clipping contributes `(2Z/M)T`; pair clipping contributes `((N−1)/M)T`. The signs of the nuclear and pair errors are different, so a one-sided monotonicity assertion would be wrong. The absolute form bound accounts for both.

Both q and q_M satisfy (5), because the clipped nuclear attraction is weaker and clipped repulsion is nonnegative. A common computable upper bound U is obtained from a normalized Slater determinant of N distinct spin-up Dirichlet orbitals with indices `(j,1,1)`, j=1,…,N. Its kinetic energy obeys

\[
t_0=\frac{\pi^2}{32R^2}\sum_{j=1}^N(j^2+2)
\le\frac{N(N+1)^2}{R^2}.
\]

For any normalized form state, the pair estimate and Cauchy–Schwarz give

\[
\sum_{i<j}\langle|x_i-x_j|^{-1}\rangle
\le(N-1)\sqrt{2N T}
\le T+N(N-1)^2/2.
\]

Dropping the attractive potential from this upper estimate shows that, for R≥1, both minima obey

\[
\lambda_N(R),\lambda_M\le
U:=2N(N+1)^2+N(N-1)^2/2.
\tag{14}
\]

The Dirichlet forms have compact resolvent: bounded-domain H¹₀ embeds compactly into L², and (5) gives form-norm control. Their normalized minimizing eigenvectors thus satisfy `T≤K0:=2(U+NZ²)`. Apply (13) to each of the two minimizers and use the variational principle in the opposite form to get

\[
\boxed{|\lambda_N(R)-\lambda_M|\le K_0(2Z+N-1)/M.}
\tag{15}
\]

This step requires no regularity of the eigenvectors beyond H¹ and no spectral gap.

## 4. Explicit bounded-potential Galerkin lower and upper bounds

The clipped potential is a bounded real multiplication operator, with

\[
\|V_M\|\le B:=M\bigl(NZ+N(N-1)/2\bigr).
\tag{16}
\]

Take all one-particle Dirichlet sine orbitals with three integer indices in `{1,…,K}`, times the two spin basis vectors. Let P be the orthogonal projector onto all N-electron Slater determinants from these orbitals and Q=I−P, with K≥N so the anchor in (14) is included. Its exact dimension is

\[
m=\binom{2K^3}{N}.
\tag{17}
\]

P commutes with the Dirichlet kinetic operator. A determinant outside P contains at least one orbital with one coordinate index≥K+1. The complete Dirichlet sine basis therefore gives

\[
QTQ\ge\Lambda Q,\qquad
\Lambda:=\frac{9(K+1)^2}{32R^2},
\tag{18}
\]

using π²>9. Let λ_P be the smallest eigenvalue of the **true** compressed clipped operator P(T+V_M)P. It is ≤U by the included anchor. For η>0 and any state u+v with u=Pψ,v=Qψ, the only off-diagonal term is V_M and

\[
2|\langle u,V_Mv\rangle|
\le\eta\|u\|^2+(B^2/\eta)\|v\|^2.
\]

Thus

\[
\lambda_M\ge\min\{\lambda_P-\eta,\Lambda-B-B^2/\eta\}.
\tag{19}
\]

Choose K≥N by integer search until

\[
\Lambda\ge U+B+B^2/\eta.
\tag{20}
\]

The search terminates by (18), and (19) and the variational upper bound give

\[
\boxed{\lambda_P-\eta\le\lambda_M\le\lambda_P.}
\tag{21}
\]

This explicitly controls the omitted infinite-dimensional subspace. The finite matrix is a rigorously bounded approximation to the actual continuum form, not a replacement of the theorem's Hamiltonian by a finite surrogate.

## 5. Proposed `BoxEnclose` and remaining implementation obligation

Here is a concrete mathematical specification for `BoxEnclose(N,Z,R,ε)` with N≥1, integer Z≥1, rational R≥1 and rational ε∈(0,1). The recursive algorithm handles N=0 separately. All parameter choices below are rational/integer decisions.

1. Form U,K0 and choose integer `M≥8K0(2Z+N−1)/ε`. Equation (15) contributes at most ε/8.
2. Set η=ε/8, form B, and find integer K≥N satisfying (20). Equation (21) contributes interval width ε/8.
3. Form the real symmetric m×m compressed matrix in the orthonormal Slater basis. Compute a symmetric rational matrix A whose entry errors are at most `e/m`, where e=ε/32. Then `||A−P(T+V_M)P||≤e` and their lowest eigenvalues differ by at most e.
4. Bisect the lowest eigenvalue of A by **exact rational PSD decisions** on A−tI, starting with [−B−1,U+1], until the bracket [lo,hi] has width≤ε/8. Exact symmetric elimination first rejects any negative diagonal. It decides PSD even with zero pivots: a zero diagonal with nonzero off-diagonal entry is not PSD; a zero row/column can be removed; otherwise use a positive pivot and Schur complement. There is no real-number sign oracle.
5. Return `[lo−e−η−ε/8, hi+e+ε/8]`. Equations (15),(21) and matrix perturbation show this encloses λ_N(R). Its width is at most `ε/8+2e+η+ε/4=9ε/16<ε`.

To make step 3 genuinely effective, one possible interval-quadrature specification is as follows. Each one-particle spatial orbital is

\[
(2R)^{-3/2}\prod_{a=1}^3\sin\!\left[\frac{\pi k_a(x_a+2R)}{4R}\right].
\]

For matrix entries, the product of two normalized Slater determinants has overall rational factor `(2R)^(−3N)/N!`; no square root of a normalization constant needs an exact-sign decision. Sum over all `2^N` spin assignments. Kinetic entries are diagonal sums of explicit π² multiples. For each spin assignment the absolute determinant-product factor is at most

\[
C_0=N!(2R)^{-3N}.
\]

Its partial derivative in any Cartesian coordinate has absolute value at most `C0 πK/(2R)`. The clipped potential has coordinate Lipschitz constant at most `M²(Z+N−1)` and absolute bound B. Consequently its product with the determinant product has coordinate Lipschitz bound

\[
L=C_0\left[M^2(Z+N-1)+\frac{B\pi K}{2R}\right].
\tag{22}
\]

Use π<4 for a rational upper bound. On a uniform Cartesian midpoint grid with J subdivisions per coordinate of Ω_R^N, the integral error, summed over spin, is at most

\[
2^N(4R)^{3N}\frac{(3N)2R}{J}\,L.
\tag{23}
\]

Choose J by this explicit rational bound to allocate at most half the required entry error to quadrature. Evaluate each midpoint with interval arithmetic to the remaining half error after multiplying by cell volume and summing. At rational grid points a distance square is rational. If it is≤M^(−2), the clipped value is exactly M; otherwise interval bisection for a positive square root and reciprocal is effective. Trigonometric values can be enclosed by Taylor series with factorial remainder, using a rational Machin-series enclosure for π. Determinants are finite sums/products. Finite sums of interval widths supply a stopping rule; it does not require knowing the exact matrix-entry sign. This describes one intentionally expensive computable construction, including a modulus for the quadrature.

**Outstanding executable obligation.** Implement steps 1–5, interval sine/π/distance evaluation, (22)–(23), determinant enumeration and exact PSD bisection with proved outward rounding and machine integer semantics. Audit the actual code and test it against independently established small problems. No such code is claimed to have been run in this milestone. An agreement that these standard routines ought to work is not a machine-verification result.

The direct continuum proofs in §§1–4 and the quadrature estimates can be reviewed separately from that implementation. Until the project has audited the complete bounded-box construction and its realization, the project-level algorithm statement below remains conditional on the `BoxEnclose` contract, rather than labeling a verified executable algorithm as complete.

## 6. Recursive algorithm conditional on the bounded-box contract

Assume `BoxEnclose` is a total rational routine satisfying the contract in §5 for the actual fermionic Dirichlet energy. Define:

```text
AtomicEnclose(N,Z,p):
    if N == 0: return [0,0]
    eps := 2^(-p-3)
    [c,d] := AtomicEnclose(N-1,Z,p+3)
    R := 2^(p+3) * N * (Z+1)
    [a,b] := BoxEnclose(N,Z,R,eps)
    return [ min(a,c-N*Z/R) - 5*N/(4*R^2), min(b,d) ]
```

Induction on N proves termination: recursion reduces N, all finite searches have explicit growth bounds, and the conditional box routine is total. Each call has both source widths≤eps. Its choice R gives `NZ/R≤eps` and `5N/(4R²)≤eps` (indeed R≥2^(p+3)N and p≥1). Equation (11) gives output width≤3eps<2^(−p). All output endpoints are rational; no unknown analytic constant or separator occurs in the code.

**Conditional theorem.** A correct total realization of the specified bounded-box routine yields one uniform deterministic algorithm for energy enclosure of every finite integer-input point-nucleus atom (including unbound cases), with no spectral-gap input. This is a finite-input computability statement and not fixed-N polynomial precision cost. This theorem does not depend on any claimed RWA lemma in the frozen project.

If §5 is accepted as a complete effective mathematical construction, it also supplies a paper computability proof. This milestone conservatively distinguishes that paper construction from an implemented, tested and formally verified algorithm. No claim of novelty for computability is made.

## 7. Parameter sizes and bit-cost boundary

Use binary integers, reduced rationals, schoolbook integer addition/multiplication/division, gcd reduction, array/index operations and output writing. A future implementation must charge these operations by operand bit length; counting one integral, one determinant or one rational operation as unit cost would be invalid.

The explicit size parameters are

\[
R=2^{p+3}N(Z+1),\quad U=2N(N+1)^2+N(N-1)^2/2,
\]
\[
M\ge8K_0(2Z+N-1)/\varepsilon,\quad
B=M(NZ+N(N-1)/2),
\]
\[
K+1\ge\sqrt{(32R^2/9)(U+B+B^2/\eta)},\quad
m=\binom{2K^3}{N},\quad \eta=\varepsilon/8.
\]

The recursive precision for a k-electron subproblem is `p+3(N−k)`; charge stays Z. There is no gap parameter. At fixed N,Z these schedules allow `R=O(2^p)`, `M=O(2^p)`, and choosing `K=O(2^(5p/2))`; constants depend on N,Z and recursion depth. Consequently the specified dense determinant representation can already have exponential size in p. Its grid is in 3N dimensions and (23) has a factor `2^N N!` after cancellation of volume scales. These transparent losses rule out presenting this construction as a proof of polynomial precision cost.

No optimized or complete machine bit-cost upper bound is claimed. The parameters exhibit all currently used N,Z,p dependence and identify the dimension/integration cost that a later efficient alternative must overcome. The fixed-shift conditional theorem in the scope report addresses what would instead be required for polynomial precision cost.

## 8. What has actually been checked

The IMS constant and fermionic subset argument, the clipping coefficient using (12), the common-anchor requirement and the Galerkin complement estimate were separately examined by the spectral-computation audit subtask. Its mathematical comments prompted explicit statements of subgroup antisymmetry, the two clipping signs, and the common upper bound. This is paper review, not proof by agent agreement.

No numerical integration, eigenvalue computation, Lean build, axiom audit or full solver execution was performed for this file. The companion `schedule_arithmetic_check_v1.py` was run using Python exact fractions: 7,200 parameter cases (1≤N,Z≤15 and 1≤p≤32) passed the finite scalar budget checks; its JSON result is `schedule_arithmetic_result_v1.json`. This finite check is not a proof of the general inequalities or continuum algorithm. Future corrections require a new version, referencing this version's SHA-256.
