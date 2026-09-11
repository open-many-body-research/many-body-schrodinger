> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exact electronic structure: a boundary audit

This is the original audit. Its unexecuted Gaussian stage is addressed by the subsequent [Gaussian-stage report](GAUSSIAN_STAGE.md), including certified integrals, extended Lean proofs, and a quantitative failure of continuum transfer for the constructed instance. Original build logs refer to the earlier source versions retained in the original archive; current-source evidence is in `formal/gaussian-logs`.

The strongest outcome delivered here is **partial (d)**. There are precise unconditional obstructions to the literal formulations of (a) and (b), a sourced conditional complexity boundary for finite-basis electronic structure, and compiled Lean proofs of explicitly limited mathematical components. **This is not a completed, machine-verified solution or hardness theorem for the unrestricted continuum Coulomb problem.** No classification satisfying (c) has been established here.

The distinction is substantive: the continuum operator, its domain, self-adjointness and ionization theorem are defined and proved or sourced in the human-readable mathematics, but are **not** defined and verified in the Lean project. The project does not hide these missing proofs in axioms or theorem hypotheses labeled as established physics. Therefore the original end-to-end formalization requirement remains unmet.

| Status | Delivered evidence |
|---|---|
| **PROVEN (Lean-checked)** | 27 scalar and real quadratic-form theorems, including the finite-output obstruction, compression counterexample, error transfer and exact dimer-block minimum. |
| **PROVEN (paper proof only)** | Continuum definitions and operator argument; ionization and hydrogen proofs; runtime interpretation; sourced complexity reductions and their conditional consequences. |
| **EMPIRICAL** | Floating-point dimer comparisons and the cited molecular benchmarks. Exact rational Python checks are reproducible computations outside Lean's kernel. |
| **CONJECTURED / OPEN** | Complexity-class separations; the final bound-molecule continuum reduction; general efficient, certified ground-state computation and a complete tractability classification. |

## Research and the exactness gap

Primary-source searches covered 9 September 2024–9 September 2026, with older foundational papers identified separately. Publication histories, recent revisions and theorem hypotheses were checked where accessible. This was a targeted audit of the requested topics, not an exhaustive bibliography or a proof of absence of further results. Full reading and access records are in the linked research files.

| Topic | Representative recent primary source | Evidence and boundary |
|---|---|---|
| FCI / selected CI | [CDFCI, arXiv:2605.04483](https://arxiv.org/abs/2605.04483) | Finite-matrix methods and measured speedups; a full orbital-basis calculation still needs a continuum error certificate. |
| FCIQMC | [10.1021/acs.jctc.4c01462](https://doi.org/10.1021/acs.jctc.4c01462), 2025 | Stochastic active-space improvements. Rigorous older convergence analysis has accuracy, overlap and spectral assumptions. |
| Ab initio DMRG | [arXiv:2506.16026](https://arxiv.org/abs/2506.16026) | Improved finite-basis benchmarks; bond dimensions and optimization costs are not uniformly controlled. |
| Coupled cluster | [arXiv:2311.00637v3](https://arxiv.org/abs/2311.00637v3), December 2025 revision | Substantial conditional local error analysis; identifying the correct root and evaluating stability constants remain necessary. |
| Neural wavefunctions | [FiRE, arXiv:2504.06087](https://arxiv.org/abs/2504.06087); [Fermi Sets, arXiv:2601.02508v2](https://arxiv.org/abs/2601.02508v2) | Empirical efficiency and restricted approximation theorems; neither supplies total time to certified ground-state accuracy. |
| Neural/DMC certificates | [arXiv:2607.25872](https://arxiv.org/abs/2607.25872) | A vanishing amplitude-optimization gap can leave phase error. |
| Quantum electronic structure | [arXiv:2607.15358](https://arxiv.org/abs/2607.15358) | Improved finite plane-wave QPE normalization; continuum error, preparation and precision costs remain separate. |
| QPE precision | [10.22331/q-2026-06-15-2140](https://doi.org/10.22331/q-2026-06-15-2140) | Proven inverse-precision black-box query bound; this is not a lower bound for all explicit-coordinate Coulomb algorithms. |
| Exact DFT | [10.1007/s11005-026-02051-1](https://doi.org/10.1007/s11005-026-02051-1) | Rigorous representation results for a specified 1D spinless class; no polynomial functional-evaluation algorithm follows. |

The [classical-method audit](research/classical.md), [neural audit](research/neural.md), [quantum/DFT audit](research/quantum_dft.md), and [complexity audit](research/complexity.md) include IDs/DOIs, theorem qualifications, empirical distinctions and access failures. They cover the original FermiNet, PauliNet, Psiformer and LapNet papers, successors, Hohenberg–Kohn, Levy and Lieb, and all requested foundational complexity papers. LapNet's full journal text, the original Kato PDF, and Lieb's original DFT full text were not obtained; no detailed theorem was attributed to an unread passage. A [separate note](research/certification.md) examines an August 2026 continuum-certification claim without presenting it as independently reproduced.

The sharp gap is **an effectively obtainable two-sided enclosure of the full continuum ground energy, together with ground-state identification and a proved total cost**. Representation, minimization and certification are distinct. Agreement of accurate methods can be powerful empirical evidence while supplying none of the missing lower bound. Conversely, some restricted continuum certificates exist or are claimed; the gap is not simply an absence of all rigorous numerics.

Here is a precise obstruction to the common inference from a finite calculation. On the real two-dimensional unit sphere, let

\[
q_0(x,y)=0,\qquad q_K(x,y)=-Ky^2,\quad K>0.
\]

Both forms restrict to zero on the subspace \(y=0\), but their ground energies are \(0\) and \(-K\). A rule seeing only that identical compression cannot approximate both ground energies within \(\varepsilon<K/2\). This theorem is **PROVEN (Lean-checked)**. It is a counterexample to an inference about arbitrary compressions, not a claim that these matrices arise from two molecular Coulomb potentials.

Proof: on \(x^2+y^2=1\), \(0\le y^2\le1\), hence \(-K\le-Ky^2\), with equality at \((0,1)\). The zero form is identically zero. If the same estimate \(e\) were within \(\varepsilon\) of both, the triangle inequality would imply \(K\le2\varepsilon\). The formalization also proves the converse: the two intervals intersect exactly when \(K\le2\varepsilon\), attained by \(e=-K/2\).

Zero residual is insufficient as well: \(\operatorname{diag}(0,1,10,11)\), compressed to the last two coordinates, has two exact Ritz eigenpairs of energies 10 and 11, both with zero full residual. Its true ground energy is 0. This elementary example is reproduced by the validation script. A ground-energy claim needs a proof excluding lower spectrum, not merely another converged Ritz pair.

## Continuum mathematics and unconditional obstructions

The full definitions, regularization details and human-readable proofs are in [Continuum definition and two unconditional boundaries](research/analytic.md), which is part of this deliverable and precedes any physical interpretation of the Lean statements. The following statements summarize that mathematics.

For positive integers \(N,M\), positive finite real \(Z_A\), fixed \(R_A\in\mathbb R^3\), and counting measure on \(\Sigma=\{\uparrow,\downarrow\}\), use

\[
\mathcal H_N=\{\psi\in L^2((\mathbb R^3\times\Sigma)^N;\mathbb C):
U_\pi\psi=\operatorname{sgn}(\pi)\psi\ (\pi\in S_N)\}.
\]

The operator domain is \(D(H)=H^2(\mathbb R^{3N};\mathbb C^{2^N})\cap\mathcal H_N\); its form domain is the corresponding \(H^1\) space. Coulomb values on collision null sets are irrelevant to the multiplication operator. Hardy's inequality on coordinate slices makes each Coulomb term infinitesimally Laplacian-bounded, so Kato–Rellich gives the self-adjoint lower-semibounded operator on this domain. The displayed Hamiltonian omits nuclear repulsion, and all energies here follow that convention. There is no box, orbital projection or Coulomb cutoff in this definition.

Write \(\mathcal E_N=\inf\sigma(H_N)\), with vacuum energy \(\mathcal E_0=0\). A ground state is a normalized domain vector satisfying \(H_N\psi=\mathcal E_N\psi\). The spectral infimum can exist without such a vector. HVZ gives essential spectrum \([\mathcal E_{N-1},\infty)\) in this full fermionic space. Strict binding guarantees a ground eigenvalue; \(N<1+\sum_AZ_A\) is a sufficient binding condition. These analytic foundations and their precise references are **PROVEN (paper proof only)** here, not imported Lean facts.

**Theorem A — failure of universal ground-vector existence.** For an atom of charge \(Z>0\), if \(\mathcal E_N\) is an eigenvalue then \(N<2Z+1\). Therefore \(N=3,M=1,Z_1=1,R_1=0\) is an instance of the original Hamiltonian with no normalized ground state. This is Lieb's ionization theorem, including threshold eigenvalues. [Lieb, DOI:10.1103/PhysRevA.29.3018](https://doi.org/10.1103/PhysRevA.29.3018); [Nam, arXiv:1009.2367, §2.1](https://arxiv.org/pdf/1009.2367).

The supplied proof uses bounded weights \(w_\eta(r)=r/(1+\eta r)\). It proves weighted kinetic positivity, tests each particle's eigenvalue equation, and lets \(\eta\downarrow0\) by monotone convergence. The resulting inequality is

\[
\int\sum_{i<j}\frac{|r_i|+|r_j|}{|r_i-r_j|}|\psi|^2\le NZ.
\]

For \(N\ge2\), the left side is strictly greater than \(N(N-1)/2\), since equality in the triangle inequality occurs on a null set. No decay or positive ionization gap is assumed. This disproves the existence premise of universal (a); it does not exclude formulas for bound instances. **PROVEN (paper proof only).**

**Theorem B — failure of the literal precision-only cost bound.** In the ordinary finite-string bit model, no uniformly correct numerical-energy algorithm can have runtime bounded solely by any function of \(N\) and \(\log(1/\varepsilon)\), independent of charge/input length, on the stated unrestricted input family.

For \(N=M=1\), the report proves by square completion that

\[
\phi_Z(r,s)=(Z^3/\pi)^{1/2}e^{-Z|r|}\chi(s),\qquad
\mathcal E_1(Z)=-Z^2/2,\qquad \|\chi\|=1.
\]

Fix \(\varepsilon=1/4\) and let \(Z\) range over positive integers. Distinct energies differ by at least \(3/2\), so distinct charges require distinct decoded outputs. Fixed runtime allows only finitely many strings, a contradiction. Among all \(B\)-bit charges, some output needs at least \(B-1\) binary symbols. The decoder must interpret an output independently of the original input; an unevaluated instruction referring back to the input is outside this numerical-output model.

The hydrogen analysis and machine-runtime interpretation are **PROVEN (paper proof only)**. The exact scalar theorem that no finite output type can approximate all \(-(n+1)^2/2\) within \(1/4\) is **PROVEN (Lean-checked)**. The Lean theorem has no Schrödinger operator or Turing machine hidden in its definition. Allowing full input length in the runtime repairs this obstruction; it proves no superpolynomial lower bound for that repaired question. Restricting nuclear charges to a bounded set also removes this example.

Ground-state observables require a selection rule: hydrogen's two spin choices have the same ground energy and opposite \(S_z\) expectations. For a selected nondegenerate gapped state, energy-to-observable bounds additionally depend on a certified gap and observable norm; arbitrary unbounded observables need domain control. This is a mathematical qualification of the requested output.

## The complexity theorem and its missing continuum step

**PROVEN (paper proof only):** inverse-polynomial-gap local Hamiltonian problems are QMA-complete, as is the relevant finite-dimensional two-particle representability problem. [Kempe–Kitaev–Regev, quant-ph/0406180](https://arxiv.org/abs/quant-ph/0406180); [Liu–Christandl–Verstraete, quant-ph/0609125](https://arxiv.org/abs/quant-ph/0609125).

O'Gorman et al.'s electronic-structure theorem has a **supplied finite orbital basis**. Its journal nuclear-attraction extension retains that restriction. Schuch–Verstraete's continuum construction uses additional engineered potentials and spatial magnetic fields. Neither cited theorem is a reduction to the exact unrestricted, nonmagnetic, point-nucleus-only model in this problem. [O'Gorman et al., DOI:10.1103/PRXQuantum.3.020322](https://doi.org/10.1103/PRXQuantum.3.020322); [Schuch–Verstraete, arXiv:0712.0483](https://arxiv.org/abs/0712.0483). The detailed audit records the primary sections and recent related developments.

The precise conditional consequence is that a deterministic polynomial-time solver for all those encoded **finite-basis** instances, at inverse-polynomial energy precision, implies \(\mathrm P=\mathrm{QMA}\); a bounded-error quantum solver implies \(\mathrm{BQP}=\mathrm{QMA}\). These separations are conjectures, not proved facts.

Complete elementary proof: for a promise \(E\le a\) or \(E\ge b\), ask for error \(\varepsilon=(b-a)/4\) and compare the estimate with \((a+b)/2\). The two cases lie strictly on opposite sides. An inverse-polynomial promise gap makes the precision request and runtime polynomial in full input length. Compose with the cited hardness reductions. This proof assumes those published reductions; they have not been re-formalized here.

A **PROVEN (Lean-checked)** general error lemma states more precisely: if

\[
|F-(\alpha E+\beta)|\le\delta,\quad |\widehat F-F|\le\varepsilon,
\quad\alpha>0,\quad2(\delta+\varepsilon)<\alpha(b-a),
\]

then comparing \(\widehat F\) with \(\alpha(a+b)/2+\beta\) separates the source YES and NO cases. Proof: the two errors add by the triangle inequality, and multiplication by positive \(\alpha\) preserves the source energy inequalities. The formal theorem **assumes** the reduction error inequality; it does not construct a physical reduction.

For the continuum transfer, the variational inequality \(\mathcal E_N\le E_{\rm basis}\) supplies only one direction. A quantitative converse or another spectral encoding must be proved. The Lean compression counterexample isolates exactly why this missing step cannot be discarded.

No complexity-class conjecture alone excludes unspecified closed forms: expression syntax, size and evaluation cost must first be fixed. Nor does QMA-hardness exclude a tractable-subclass classification. The phrase “physically relevant” needs a precise predicate before a necessary-and-sufficient classification is a theorem statement. Thus there is no justified statement here that a single known conjecture would have to fail for all of (a)–(c).

## Human proof of the formally checked small reduction stage

The two-site Hubbard model has four spin orbitals and exactly two electrons. With hopping \(t\in\mathbb R\) and repulsion \(U>0\), a singlet block is

\[
A=\begin{pmatrix}0&-2t\\-2t&U\end{pmatrix},\quad
q(x,y)=-4txy+Uy^2,\quad
D=\sqrt{U^2+16t^2},\quad E=(U-D)/2.
\]

The Lean result starts from this **explicit real block**. It does not assume or prove its identification with the original continuum Hamiltonian.

Since \(D\ge U\), \(E\le0\). Expanding gives \(E^2-UE=4t^2\). Put \(c=U-E>0\); direct algebra yields

\[
c\,[q(x,y)-E(x^2+y^2)]=(-2tx+cy)^2\ge0.
\]

Consequently every real vector has Rayleigh energy at least \(E\). The nonzero vector \((c,2t)\) attains equality and satisfies both eigenvalue equations; division by its norm gives a normalized minimizer. This also handles \(t=0\). The complex block has the same conclusion by splitting any complex vector into real and imaginary parts; that last extension is a paper observation, while the formal theorem quantifies real vectors.

Use the shifted effective Heisenberg operator \(H_{\rm eff}=(4t^2/U)(S_1\cdot S_2-\tfrac14I)\), whose triplets have energy zero and singlet has energy \(-4t^2/U\). Its exact singlet-energy error satisfies

\[
\delta=E+4t^2/U=E^2/U\ge0.
\]

The characteristic identity and \(E\le0\) give \(-4t^2\le UE\le0\), hence \(U^2E^2\le16t^4\). Divide by \(U^3>0\) to conclude

\[
\boxed{0\le E+4t^2/U\le16t^4/U^3.}
\]

This is an exact bound for all real \(t\) and positive \(U\), with no assumption of small hopping. The lower bound, nonzero minimizing eigenvector and approximation bound are **PROVEN (Lean-checked)**.

## Computational validation and its scope

[The executable script](validation/reduction_demo.py) constructs the six-dimensional fixed-two-electron Fock matrix by applying creation/annihilation operators with occupation-parity signs. For six rational parameter choices, independent exact rational determinant expansion verifies

\[
\det(\lambda I-H)=\lambda^3(\lambda-U)(\lambda^2-U\lambda-4t^2).
\]

NumPy diagonalization independently agrees with the resulting complete spectrum, and the explicit singlet change of basis agrees with the block above. Exact rational Python checks are reproducible computations, **not** Lean kernel proofs; floating-point spectral comparisons are **EMPIRICAL**. [Results](validation/results.json), [CSV](validation/dimer_results.csv), [run log](validation/run.log).

| \(t\) | \(U\) | Hubbard ground energy | Heisenberg energy | Actual error | Proved upper bound |
|---:|---:|---:|---:|---:|---:|
| 1 | 4 | −0.828427124746 | −1 | 0.171572875254 | 0.25 |
| 1 | 10 | −0.385164807135 | −0.4 | 0.014835192865 | 0.016 |
| 1 | 20 | −0.198039027186 | −0.2 | 0.001960972814 | 0.002 |
| 1 | 100 | −0.039984012787 | −0.04 | 0.000015987213 | 0.000016 |

The largest floating-point discrepancy from the exact spectrum is below \(3.6\times10^{-15}\). Additional cases \(t=0\) and \(t=-1,U=10\) check the zero-hopping limit and hopping-sign symmetry. Energies are in model units. If one model unit is assigned one hartree, errors above 1 mHa occur in the first three displayed rows and also the sign-reversed \(U=10\) case. They are the expected, rigorously bounded finite-\(U\) corrections to the effective model, not discrepancies in the exact Hubbard solution.

This demonstrates the Hubbard–Heisenberg stage only. The Gaussian-orbital construction, all Coulomb integrals, and its error inequalities are not executed; neither is any continuum reduction. Consequently this does not fulfill the requested complete small-instance demonstration of an original-model hardness reduction. No general new solver was produced, so there is no fabricated table for H, H₂, He, LiH, H₂O, N₂ or H₁₀, and no comparison of unlike Hamiltonians with experiment.

## Formal source, toolchain and audit

The complete scientific sources are [Boundary.lean](formal/Boundary.lean) and [HubbardDimer.lean](formal/HubbardDimer.lean). Definitions are explicit and limited to scalar energy sequences and real quadratic forms. The hydrogen output theorem proves an actual finite-codomain impossibility; the dimer theorem proves a universal Rayleigh lower bound with an attained nonzero eigenvector. Neither is a placeholder definition of a Coulomb solution.

The pinned toolchain is Lean **v4.34.0-rc2**, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; Mathlib commit **`d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`**. This is the current Mathlib commit selected during the run and uses a Lean release candidate. Exact transitive dependencies are in [lake-manifest.json](formal/lake-manifest.json). Installation details are in [SETUP.md](formal/setup-logs/SETUP.md).

Every scientific top-level theorem is described in plain English in [BOUNDARY_STATEMENTS.md](formal/BOUNDARY_STATEMENTS.md) and [DIMER_STATEMENTS.md](formal/DIMER_STATEMENTS.md), including what is assumed and what is absent. The [build log](formal/setup-logs/lake-build.log) records the actual scientific targets and successful build; [versions](formal/setup-logs/versions.log) records the toolchain. The [axiom audit](formal/setup-logs/axiom-audit.log) and [source audit](formal/setup-logs/source-audit.json) record all 27 theorem dependencies and source hashes. There are no `sorry`, added `axiom` declarations or `native_decide` calls in the delivered scientific sources. Audited theorem dependencies are confined to Mathlib's standard `propext`, `Classical.choice` and `Quot.sound`.

The missing formal objects are specifically the antisymmetric continuum \(L^2\) operator and Sobolev domains, its Coulomb multiplication and Kato–Rellich proof, the weighted ionization argument and measure-theoretic limits, hydrogen's analytic spectral identification, the complexity reductions and machine cost model, and the Fock-to-block identification. They remain explicit limitations rather than silently assumed facts.

## Points requiring particular care

| Temptation | Resolution in this work |
|---|---|
| Equate infimum with an eigenvector | Defined both and supplied an original-model counterexample. |
| Test an eigenfunction with an unbounded radial weight | Used bounded weights and proved the limiting argument. |
| Assume strict binding or decay in an ionization proof | Included threshold eigenstates and avoided moment assumptions. |
| Infer a uniform strict triangle margin | Used the null equality set and normalization instead. |
| Treat FCI as the full continuum answer | Kept the orbital projection and missing converse error bound explicit. |
| Treat tiny residuals or diagnostics as ground-state certificates | Required spectral identification; supplied a zero-residual counterexample. |
| Treat neural universality as energy accuracy | Distinguished compact uniform norms, kinetic energy, tails and optimization. |
| Treat VMC/DMC agreement as exactness | Retained statistical errors and nodal/phase bias. |
| Treat full CC coordinates as an efficient solution | Separated a reparameterization from discovering its amplitudes. |
| Treat simulation precision as QPE energy precision | Kept time, overlap, normalization and oracle assumptions. |
| Transfer finite-basis hardness to the continuum | Stated the absent reduction and formalized the error needed by one. |
| Claim a complexity separation | Made P=QMA/BQP=QMA conclusions conditional and model-specific. |
| Ignore input lengths or ground-space degeneracy | Gave explicit hydrogen counterexamples and encoding assumptions. |
| Accept a headline as a proof | Recorded access failures, conditional gaps, and a withdrawn ionization preprint. |
| Call a compiled algebra lemma the whole physics theorem | Listed every unformalized link and declared the deliverable partial. |
| Call a setup check the scientific build | Made the scientific modules the default Lake build targets. |
| Call the dimer a complete reduction | Identified the demonstrated first stage and the absent Gaussian/continuum stages. |

## Remaining open theorem

**Prove or refute:** there exist polynomials \(p,q\) and a deterministic polynomial-time map taking every encoded promise 2-local Hamiltonian instance \(x\) to positive rational nuclear charges, pairwise distinct rational positions, a positive integer electron number \(N\), and rational thresholds \(A<B\), with total encoding length at most \(p(|x|)\), such that the full antisymmetric, nonmagnetic, fixed-point-nuclei Coulomb Hamiltonian \(H_x\), without an orbital restriction, satisfies

\[
B-A\ge1/q(|x|),\qquad
x\in\mathrm{YES}\Rightarrow\inf\sigma(H_x)\le A,\qquad
x\in\mathrm{NO}\Rightarrow\inf\sigma(H_x)\ge B,
\]

and, on every promised image, the ionization margin obeys

\[
\mathcal E_{N-1}(H_x)-\mathcal E_N(H_x)\ge1/q(|x|).
\]

Here \(\mathcal E_{N-1}(H_x)\) means the same nuclei with one fewer electron. This asks for a continuum hardness reduction whose images are bound molecules; the binding requirement is an additional, explicitly unproved strengthening. It pinpoints the missing physical encoding and continuum-error control rather than assuming either.
