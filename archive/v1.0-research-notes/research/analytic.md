> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Continuum definition and two unconditional boundaries

Status: **PROVEN (paper proof only)** throughout this file. No assertion in this file is claimed to have been formalized in Lean. The proofs below are independent derivations of elementary consequences of standard analytic foundations; the HVZ and Zhislin results are explicitly cited background theorems, not supplied with full proofs here.

## 1. Exact continuum object

Let N,M be positive integers, let Z_A be finite positive real numbers, and let R_A belong to R³. Nuclear locations may be assumed pairwise distinct for a physical molecule, but this is not needed to define the electronic operator. Put S={↑,↓}, with counting measure, and give R³ Lebesgue measure. Set X_N=(R³×S)^N, and identify L²(X_N;C) with L²(R^{3N};C^{2^N}). Define the closed fermionic subspace

    H_N = {ψ ∈ L²(X_N;C) : U_π ψ = sgn(π) ψ for every π∈S_N},

where U_π simultaneously permutes each electron's position and spin. Equivalently this is the range of the orthogonal projection P_-=(1/N!)Σ_π sgn(π)U_π. Define H_N^s=H^s(R^{3N};C^{2^N})∩H_N, where H^s is the standard L² Sobolev space of spatial weak derivatives through order s. The spin coordinates have no derivatives.

On domain D(H)=H_N², define

    Hψ = -½ Σ_i Δ_iψ + Vψ,
    V = -Σ_{i,A} Z_A/|r_i-R_A| + Σ_{i<j} 1/|r_i-r_j|.

Values assigned to V on collision sets of Lebesgue measure zero do not change the multiplication operator. There is no nuclear-nuclear repulsion constant in this definition, matching the user's displayed Hamiltonian. Its addition changes electronic energies by that fixed constant, not electronic eigenfunctions.

Hardy's inequality in R³ gives ||u/|x-a|||₂ ≤ 2||∇u||₂. Applying it to slices in the i-th coordinate, including when a=r_j, gives a finite constant C(N,Z) with ||Vψ||₂≤C||∇ψ||₂. Fourier Cauchy-Schwarz gives ||∇ψ||₂²≤||ψ||₂||-Δψ||₂, so Young's inequality implies, for every a>0, ||Vψ||₂≤a||-Δψ||₂+b_a||ψ||₂. Thus V is infinitesimally bounded relative to -Δ. It is real and symmetric on H², and invariant under electron permutations. Kato-Rellich therefore gives a self-adjoint operator on exactly H_N², bounded below. Its closed quadratic form has domain H_N¹ and is

    q_N[ψ] = ½Σ_i||∇_iψ||₂² + ∫V|ψ|².

For the lower bound, Hardy plus Cauchy-Schwarz bounds each attractive Coulomb integral by a constant times ||ψ||||∇ψ||, and Young's inequality absorbs any desired positive fraction of the kinetic term. The repulsive terms are nonnegative. Smooth compactly supported functions on all spatial configuration space, followed by P_-, give a core. One should not silently substitute smooth functions supported away from all collision sets as an operator core: removal of codimension-three sets requires care for H², although form-core statements are easier.

The historical foundation is Kato, *Fundamental properties of Hamiltonian operators of Schrödinger type*, Trans. AMS 70 (1951), 195–211, DOI [10.1090/S0002-9947-1951-0041010-X](https://doi.org/10.1090/S0002-9947-1951-0041010-X) (also DOI 10.2307/1990366). The journal PDF endpoint returned HTTP 403 during this run; bibliographic metadata and the stated self-adjointness scope were verified, but the original PDF was not read. The Hardy/Kato-Rellich argument is stated explicitly above rather than claiming to have read that unavailable source.

Define E_N=inf σ(H)=inf{q_N[ψ]:ψ∈H_N¹,||ψ||₂=1}, and define E_0=0. A normalized ground state means a vector ψ∈D(H), ||ψ||₂=1, Hψ=E_Nψ. The real number E_N exists whether or not this infimum is attained by a vector.

For this fixed-nuclei repulsive-electron problem, the fermionic HVZ theorem gives σ_ess(H_N)=[E_{N-1},∞). This statement uses the full spin-antisymmetric space, not a separately constrained total-spin or angular-momentum sector. In particular E_N<E_{N-1} implies that E_N is an isolated eigenvalue of finite multiplicity. The converse implication “ground eigenvector implies strict binding” is false without excluding threshold eigenvectors. Zhislin's theorem gives strict binding when N<1+Σ_A Z_A; it is a sufficient condition, not an exact classification of bound molecular ions.

Primary modern text explicitly stating and using the atomic HVZ/Zhislin facts is Nam, *New bounds on the maximum ionization of atoms*, arXiv:[1009.2367](https://arxiv.org/abs/1009.2367), pp.1–2, [full PDF](https://arxiv.org/pdf/1009.2367). Molecular Hilbert space, domains, HVZ and Zhislin statements were read directly in Anapolitanos, Olivieri and Zalczer, *On boundedness of isomerization paths for non- and semirelativistic molecules*, arXiv:[2212.11938v2](https://arxiv.org/abs/2212.11938), [full PDF](https://arxiv.org/pdf/2212.11938), pp.5–7, equations (1.10)–(1.15), Theorems 1.1 and 1.4. Its 2025 journal DOI is [10.1016/j.jfa.2024.110713](https://doi.org/10.1016/j.jfa.2024.110713); the DOI endpoint failed to return text, so the version actually read was the March 2023 arXiv version. The molecular results above are standard background, not newly established theorems here.

## 2. An original-model obstruction: H^{--} has no normalized ground state

**Theorem (Lieb's ionization bound, including threshold).** For the atomic instance M=1, R_1=0, Z_1=Z>0, if E_N is an eigenvalue, then N<2Z+1. Consequently the specified original Coulomb operator with N=3, M=1 and Z_1=1 has no normalized ground state. This disproves the universal existence assertion implicit in (a); it does not prove a computational hardness result for those instances that do bind.

This is Lieb's theorem, DOI [10.1103/PhysRevA.29.3018](https://doi.org/10.1103/PhysRevA.29.3018). Its direct applicability to eigenvalues at threshold, and a proof of the atomic bound, were verified in Nam, arXiv:1009.2367, pp.2 and 4, §2.1. Nam explicitly states that strict binding is not assumed. The proof below uses bounded multipliers to make the potentially delicate unbounded |r_i| test rigorous without assuming moments or exponential localization.

**Lemma A (monotonicity).** E_N≤E_{N-1}.

Proof. Choose a normalized smooth compactly supported antisymmetric (N−1)-electron trial function Φ of energy at most E_{N-1}+δ. Its spatial support has all coordinates in a ball of radius K. Choose a normalized one-electron spinor g supported in a ball of radius 1, and put g_L(x,s)=L^{-3/2}g((x-L²e_1)/L,s). Its support is disjoint from that ball for large L and its kinetic energy is O(L^{-2}). Antisymmetrize Φ⊗g_L, with normalization 1/√N for the sum of its N disjoint position-support components. Cross terms between these components vanish, including kinetic cross terms. In every component the new electron lies at distance at least L²−L−K from each old electron, so new pair repulsion is bounded by (N−1)/(L²−L−K). Its nuclear attraction is nonpositive and may be discarded for an upper bound. Hence E_N≤E_{N-1}+δ+O(L^{-2}). Let L→∞ and δ↓0. For N=1 the same distant packet gives E_1≤E_0=0. ∎

**Lemma B (bounded weighted kinetic positivity).** For ε>0 let w_ε(r)=r/(1+εr). For f∈H²(R³),

    Re⟨w_ε f,−Δf⟩ ≥ ε∫|f(x)|²/(1+ε|x|)³ dx ≥0.

Proof. First take smooth f with support away from 0. Integration by parts gives

    Re⟨wf,−Δf⟩ = ∫w|∇f|² − ½∫(w''+2w'/r)|f|².

Expanding the nonnegative square with X=x/r² gives

    ∫w|∇f+Xf|² = ∫w|∇f|² − ∫(w'/r)|f|²,

because div(wX)=w'/r+w/r². Subtraction yields the exact identity

    Re⟨wf,−Δf⟩ = ∫w|∇f+Xf|² − ½∫w''|f|².

Here w''=−2ε/(1+εr)³, establishing the inequality. To extend to H², the right-hand expression may equivalently be treated as the continuous H¹ quadratic form ∫w|∇f|²−∫|f|²/[r(1+εr)³]. The singular term is continuous under H¹ convergence by Hardy and Cauchy-Schwarz. Approximation by smooth functions with a small ball removed is valid in H¹ in dimension three (a radial cutoff on r≤2δ contributes O(δ) to the squared H¹ norm for smooth bounded functions); outer cutoffs handle infinity. The identity's left side for H² agrees with that form by weak integration by parts since w is bounded and Lipschitz. No point mass occurs in Δw at zero, as the flux across radius δ is O(δ²). ∎

**Proof of the theorem.** Assume a normalized ground eigenfunction ψ∈H_N² exists. For each i, decompose H_N=H_{N-1}^{(i)}−½Δ_i−Z/r_i+Σ_{j≠i}1/r_ij, where H_{N-1}^{(i)} omits particle i. Use w_ε(r_i)ψ as a weak-form test in (H_N−E_N)ψ=0 and take the real part. This is legitimate because w_ε is bounded Lipschitz and all Coulomb form terms are finite. Although this individual test vector need not be fully antisymmetric, the eigenvalue equation is an equality in the full L² space as well: the fermionic operator is the restriction of the full permutation-invariant operator. For almost every value of particle i, the remaining slice is antisymmetric in its N−1 coordinates. Therefore

    Re⟨w_ε(r_i)ψ,(H_{N-1}^{(i)}−E_N)ψ⟩≥0

by the variational lower bound and Lemma A. There is no derivative of w_ε in those N−1 coordinates. Lemma B makes the particle-i kinetic term nonnegative. Consequently

    ∫Σ_{j≠i} w_ε(r_i)/r_ij |ψ|² ≤ Z∫w_ε(r_i)/r_i |ψ|².

Sum this over i:

    ∫Σ_{i<j}(w_ε(r_i)+w_ε(r_j))/r_ij |ψ|²
      ≤ Z∫Σ_i 1/(1+εr_i)|ψ|² ≤ ZN.

Let ε↓0 along 1/k. Monotone convergence on the nonnegative left side gives

    ∫Σ_{i<j}(r_i+r_j)/r_ij |ψ|² ≤ ZN.                 (1)

The triangle inequality gives (r_i+r_j)/r_ij≥1 off collisions. For each pair it is strictly greater than 1 except where the two position vectors point in opposite directions or one is zero. This exceptional set has six-dimensional Lebesgue measure zero: for each nonzero r_i, the allowed r_j lie on a one-dimensional ray; then apply Fubini and account separately for r_i=0. Thus for N≥2 the integrand sum exceeds N(N−1)/2 almost everywhere. Since ||ψ||₂=1, (1) implies N(N−1)/2<ZN, hence N<2Z+1. For N=1 the conclusion follows from Z>0. For N=3,Z=1 it would assert 3<3, a contradiction. ∎

The strict inequality uses a measure-zero geometric statement and normalization, not a claimed positive uniform margin in the triangle inequality. The proof permits E_N=E_{N-1}; no assumed decay or nonzero ionization gap is used.

## 3. Hydrogen gives an unconditional input/output-size obstruction to literal (b)

**Hydrogen theorem.** For N=M=1, R_1=0, Z>0,

    E(Z)=−Z²/2,
    φ_Z(r,s)=(Z³/π)^{1/2} exp(−Z|r|) χ(s),

where χ∈C² has norm one, is a normalized ground state.

Proof. Radial integration gives its norm as 4Z³∫_0^∞r²e^{−2Zr}dr=1. It is in H²: its Hessian has at worst a 1/r singularity at zero, which is locally square-integrable in R³, and it decays exponentially. The radial Laplacian gives Δφ_Z=(Z²−2Z/r)φ_Z off zero; the vanishing flux lim_{r↓0}r²∂_rφ_Z=0 precludes a delta function there, so the eigenvalue equation holds distributionally and in L². For every smooth compactly supported f, integration by parts with div(x/r)=2/r gives

    q_Z[f]+(Z²/2)||f||² = ½∫|∇f+Z(x/r)f|²≥0.

Extend by H¹ density and Hardy to all form-domain vectors. The variational principle and the exhibited eigenvector then give E(Z)=−Z²/2. ∎

**Theorem (uniform precision-only runtime bound fails).** In a classical bit model, suppose inputs include every positive integer nuclear charge Z in binary, and an output is a finite string with an input-independent interpretation as a real numerical approximation. No total correct algorithm for the original model can have runtime bounded solely by a function of N and log(1/ε), independent of nuclear charge/input length, if the output must approximate E_N to absolute error ε.

Proof. Restrict to the hydrogen family and fix ε=1/4. If Z and W are distinct positive integers, |E(Z)−E(W)|=|Z²−W²|/2≥3/2>2ε. Therefore the same interpreted output cannot be correct for two distinct charges. A fixed runtime bound T for N=1, ε=1/4 permits only finitely many output strings (at most T output symbols over a finite alphabet), but there are infinitely many charges. This contradicts correctness. Quantitatively, among the 2^{B−1} positive B-bit charges, some output has binary length at least B−1, since there are only 2^{B−1}−1 binary strings of length less than B−1. ∎

This proves a literal parameterization defect, not superpolynomial hardness after the total input size is included. It is conditional on an ordinary finite-string output model; an unevaluated instruction to square the input is not a numerical approximation under that interpretation. Physical restrictions such as bounded nuclear charges, M≤N and neutral systems may remove this specific example. A meaningful complexity claim should include an explicit finite representation and length L for M, charges, positions, requested observable and any promised spectral gap/overlap, and then state a bound in those parameters.

## 4. State-dependent observables require a selection rule

The hydrogen theorem gives a two-dimensional ground eigenspace because χ is arbitrary. The bounded spin observable S_z=(1/2)diag(1,−1) has expectations +1/2 in φ_Z⊗↑ and −1/2 in φ_Z⊗↓, although both have the same energy. Thus “observables of Ψ₀” is not a single-valued request for a spin-independent Hamiltonian without a chosen pure ground state, specified mixed state, or quantification over the ground subspace. Ground energy alone does not resolve this.

## 5. What these results do and do not establish

* The universal normalized-wavefunction request in (a) fails on a legal original-model instance, H^{--}; a binding hypothesis repairs that defect.
* The literal runtime demand in (b) fails in the standard bit model by an unconditional input/output-size theorem; including input size repairs that defect but does not establish tractability.
* Neither theorem proves that every bound Coulomb molecule is computationally hard.
* Neither theorem rules out exact special classes or a suitably defined classification in (c).
* General symbolic “closed form” and “finitely parameterized” are not computational complexity predicates until their syntax, evaluation cost and representation restrictions are specified.
* A hardness theorem for a finite-basis projected Hamiltonian is not automatically a theorem about the unprojected continuum Coulomb operator with only point-nuclear attractions. That transfer needs an explicit reduction and a controlled basis/continuum error bound.

## 6. Hand-wave audit

1. Missing normalized ground vector: retained the distinction between spectral infimum and attained eigenvalue and gave an explicit no-ground-state instance.
2. Unbounded |r_i| multiplier: replaced it with bounded w_ε, proved the weighted kinetic inequality, and used monotone convergence.
3. Threshold states: never assumed a strict binding gap or exponential decay.
4. Strict triangle inequality: identified the equality set and supplied the Fubini null-set argument.
5. Fermionic slices: applied the lower bound in the remaining antisymmetric N−1 particle space, with spin coordinates permuted together with positions.
6. Collision set domains: separated the H² operator domain from H¹ form arguments and did not assume an unjustified operator core with collisions removed.
7. Runtime parameters: stated input and output encoding assumptions and limited the conclusion to the literal parameter omission.
8. Degenerate observables: supplied the explicit hydrogen spin counterexample.
9. Machine verification: every result in this file remains paper-proof-only; an algebraic Lean consequence supplied elsewhere cannot be substituted for the continuum analytic proof.
10. Withdrawn primary source: a search surfaced Yukimi Goto, arXiv:[2107.01826](https://arxiv.org/abs/2107.01826), apparently strengthening the molecular ionization bound. Opening the primary record revealed that v2 was withdrawn with the comment “The proof is incorrect.” That claimed improvement was excluded. This illustrates why a search-result abstract is insufficient evidence.
