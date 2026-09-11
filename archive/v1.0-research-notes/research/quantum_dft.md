> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Quantum algorithms and exact density-functional theory: primary-source audit

Audit date: 2026-09-09 UTC. Window: 2024-09-09 through 2026-09-09. This is a targeted literature map, not a claim of exhaustive coverage. Some papers entered the window through journal publication even though their arXiv v1 predates it. No theorem below was formalized by this research subtask.

## The distinction that matters

Quantum Hamiltonian **simulation** with polylogarithmic dependence on simulation error does not give ground-energy **estimation** with polylogarithmic dependence on energy error. Simulated evolution must run for an appropriately long time, the target eigenstate must receive adequate weight, and any finite-basis Hamiltonian must be related to the continuum operator with controlled error. Exact density-functional variational identities likewise do not themselves compute their universal functional. These are mathematical distinctions, not judgments about the empirical value of the methods.

## Verified recent primary sources

### Q1. First-quantized spectral amplification (July 2026)

A. Dutkiewicz et al., *Spectral amplification for ground-state energy estimation of electronic structure in first quantization*, [arXiv:2607.15358v1](https://arxiv.org/html/2607.15358v1), submitted 16 July 2026.

**PROVEN (paper proof only):** An explicit sum-of-squares representation and block encoding improve effective normalization from O(ηΔ⁻²+η²Δ⁻¹) to O(ηΔ⁻³ᐟ²+η³ᐟ²Δ⁻¹), in the stated scaling regime. Here η counts electrons; Δ is the effective spatial grid spacing. Sections II–IV construct the representation and circuits.

**EMPIRICAL/resource estimate:** Compiled examples report 2–44-fold Toffoli reductions.

**Boundary:** Equations (5)–(12) define a finite plane-wave basis in a cubic cell of volume Ω; this is not the original isolated-molecule continuum operator. For a shift −β≤E₀, the effective QPE normalization is √[(λSOS−(E₀+β))(E₀+β)]. Lower-bound quality and block-encoding cost both matter. The paper improves QPE on a low-energy state; it does not establish uniform efficient ground-state preparation, continuum convergence with a polynomial bit-complexity bound, or option (b). See specifically Eqs. (1)–(3), (9)–(12), and (22).

### Q2. Any-basis first quantization (journal 2025)

T. N. Georges et al., *Quantum simulations of chemistry in first quantization with any basis set*, [DOI:10.1038/s41534-025-00987-1](https://www.nature.com/articles/s41534-025-00987-1), npj Quantum Information **11**, 55 (2025); [arXiv:2408.03145](https://arxiv.org/abs/2408.03145) (v1 outside window).

**PROVEN (paper proof only):** LCU decomposition and block encoding for first-quantized electronic Hamiltonians in arbitrary finite orbital bases, with resource scaling exploiting sparsity.

**EMPIRICAL/resource estimate:** The paper evaluates active-space examples including [Fe₂S₂]²⁻. Its single-shot estimates do not include a general proof of initial ground-state overlap. Equation II.41 allocates error among QPE, coefficient truncation, and PREP implementation. For the active-space study, the truncation threshold is selected using unrestricted MP2 energy estimates (text following II.41), so that numerical truncation estimate must not be presented as a rigorous operator-norm error certificate. PREP here is the LCU circuit, not the chemical ground-state preparation problem. The basis and active-space errors remain distinct.

### Q3. Initial states (journal December 2024)

S. Fomichev et al., *Initial State Preparation for Quantum Chemistry on Quantum Computers*, [DOI:10.1103/PRXQuantum.5.040339](https://doi.org/10.1103/PRXQuantum.5.040339), PRX Quantum **5**, 040339 (9 December 2024); [arXiv:2310.18410v2](https://arxiv.org/html/2310.18410v2) (preprint outside window). The [published PDF](https://journals.aps.org/prxquantum/pdf/10.1103/PRXQuantum.5.040339), Section III A and Eq. (17), was also checked.

**PROVEN (paper proof only):** Circuits implement a supplied sum of D Slater determinants, with O(D log D) Toffoli complexity under the paper's access/representation assumptions, rather than discovering a good expansion of bounded D for every molecule.

**EMPIRICAL:** Energy distributions, low-precision filtering, and molecular examples improve initial-state quality/cost in selected systems.

**Boundary:** Section I explicitly starts from a classical candidate wavefunction; Sections IV–VI evaluate its energy distribution and refinement. Preparing a specified compact state and proving that a compact, efficiently discoverable state has adequate ground-space overlap are different tasks. Neither the asymptotic preparation circuit nor those examples prove a uniform end-to-end ground-state algorithm.

### Q4. Symmetry filtering (January 2026)

V. Khinevich and W. Mizukami, *Symmetry-Adapted State Preparation for Quantum Chemistry on Fault-Tolerant Quantum Computers*, [arXiv:2601.08533v1](https://arxiv.org/html/2601.08533v1), 13 January 2026.

**PROVEN (paper proof only):** Constructions implement particle-number and spin projectors using LCU/generalized signal processing, with stated circuit costs.

**EMPIRICAL:** O₂ and trimethylenemethane active-space simulations improve QPE success; FeMoco resource estimates use overlap assumptions and classical approximate states. Target symmetry-sector overlap is not automatically ground-state overlap. Section IV.7 explicitly retains amplification overhead when initial sector weight is small. Its optimistic FeMoco extrapolation is an estimate, not a universal bound.

### Q5. Precision lower bound (journal June 2026)

N. S. Mande and R. de Wolf, *Tight Bounds for Quantum Phase Estimation and Related Problems*, [DOI:10.22331/q-2026-06-15-2140](https://quantum-journal.org/papers/q-2026-06-15-2140/), Quantum **10**, 2140 (15 June 2026); [arXiv:2305.04908v3](https://arxiv.org/pdf/2305.04908v3).

**PROVEN (paper proof only):** Theorem 1.3: for dimension d≥2, angular precision δ∈(0,1), and failure probability p∈(0,1/2), every algorithm solving black-box phase estimation requires Ω(δ⁻¹ log(1/p)) queries. The model counts applications of U and U⁻¹ (controlled versions included in the formal model), and even supplies an eigenstate. Advice-guided extremal-eigenphase results expose additional overlap dependence.

**Boundary:** This rules out a polylog(1/δ) generic oracle phase-estimation algorithm. It is not an unconditional lower bound for an algorithm given explicit nuclear coordinates and charges; exploiting that special input structure need not use this oracle model. It does not by itself prove QMA-hardness of the specified continuum family.

### D1. Exact Kohn–Sham structure in a restricted continuous class (March 2026)

T. Carvalho Corso, *A rigorous formulation of density functional theory for spinless fermions in one dimension*, [DOI:10.1007/s11005-026-02051-1](https://link.springer.com/article/10.1007/s11005-026-02051-1), Letters in Mathematical Physics **116**, 27 (3 March 2026).

**PROVEN (paper proof only):** On I=(0,1), with spinless antisymmetric N-particle space, real v∈H⁻¹(I), and real pair interactions w∈W⁻¹,q(I²), q>2, Theorem 2.3 characterizes Neumann-form ground-state densities as positive H¹(I) functions of mass N, independent of w. Further theorems establish potential uniqueness (modulo constants), exchange-correlation Gâteaux differentiability, and exact Kohn–Sham representation. Periodic/antiperiodic versions have additional hypotheses.

**Boundary:** This is a precise recent restricted-class theorem, but the dimension, boundary conditions, potential classes, and lack of a polynomial functional-evaluation algorithm prevent interpreting it as option (c). The introduction identifies general three-dimensional continuum representability as unresolved. Exact representability does not supply efficient functional evaluation.

### D2. Moreau–Yosida inversion (June 2026)

V. H. Bakkestuen, M. F. Herbst, V. Falmår, M. Penz, and A. Laestadius, *Moreau–Yosida-based Kohn–Sham Inversion for Periodic Systems*, [arXiv:2606.19471v1](https://arxiv.org/html/2606.19471v1), 17 June 2026.

**PROVEN (paper proof only):** The functional-analytic framework gives proximal-map properties and convergence statements with convexity, lower semicontinuity, Hilbert/Banach-space hypotheses, and existence of appropriate subgradients. Inversion starts from a reference density.

**EMPIRICAL:** Periodic-material demonstrations recover potentials at the PBE/pseudopotential reference level with finite plane-wave cutoffs (45–83 Ha in Figure 5), and investigate conditioning and solver failures. They are not exact correlated Coulomb energies. The convergence of regularization must not be converted into a polynomial end-to-end complexity bound without rates and controlled proximal solves.

### D3. Clarification of exact DFT hierarchies (2026)

N. Sheng, *Exact density-functional theory as parallel ensemble variational hierarchies: from Lieb’s formulation to Kohn–Sham theory*, [arXiv:2603.23399v1](https://arxiv.org/html/2603.23399v1), 24 March 2026 (HTML manuscript carries an August 2026 date).

**Expository, not a new solution:** Section I explicitly describes a reorganization of existing results rather than a new theorem-driven contribution. It distinguishes pure-state and ensemble constrained searches, functional domains from representability, and exact auxiliary Kohn–Sham structure from spectral interpretation. It claims no new polynomial evaluation algorithm. Treat it as contemporary exposition, not independent evidence of a newly solved universal functional.

## Seminal sources, verified identifiers

1. P. Hohenberg and W. Kohn, *Inhomogeneous Electron Gas*, [DOI:10.1103/PhysRev.136.B864](https://doi.org/10.1103/PhysRev.136.B864) (1964). Density-to-potential uniqueness and variational structure under their hypotheses do not specify an efficiently evaluable universal functional. Publisher metadata/abstract verified here; detailed historical proof is not independently rederived in this subtask.
2. M. Levy, *Universal variational functionals of electron densities, first-order density matrices, and natural spin-orbitals and solution of the v-representability problem*, [DOI:10.1073/pnas.76.12.6062](https://pmc.ncbi.nlm.nih.gov/articles/PMC411802/) (1979). The constrained search ranges over antisymmetric wavefunctions with prescribed density. This extends admissible trial densities without solving a finite-complexity optimization problem. The historical title's “solution” must not be confused with proving every N-representable density is a ground density of an admissible potential.
3. E. H. Lieb, *Density functionals for Coulomb systems*, [DOI:10.1002/qua.560240302](https://onlinelibrary.wiley.com/doi/10.1002/qua.560240302) (1983). Establishes mathematical underpinnings of universal DFT. Publisher bibliographic record/abstract verified; full primary text was not obtained in this subtask, so detailed theorems should be sourced separately before being attributed to a specific theorem number.
4. G. H. Low and I. L. Chuang, *Hamiltonian Simulation by Qubitization*, [arXiv:1610.06546v3](https://arxiv.org/html/1610.06546v3), [DOI:10.22331/q-2019-07-12-163](https://doi.org/10.22331/q-2019-07-12-163). For a normalized Hamiltonian given through preparation/unitary oracles, simulation costs O(t+log(1/εsim)) queries in the abstract's bound. Physical Hamiltonians introduce the block-encoding normalization into time. This is simulation error, not ground-energy error.

## Explicit access, precision, and certification accounting

The following is an elementary synthesis/derivation, rather than a quotation of a universal theorem from any one paper.

Let K=P H P be a finite-dimensional compression, and suppose a circuit prepares a normalized |φ⟩ with ground-space weight w=⟨φ|Π₀|φ⟩>0. Ideal spectral measurement hits the ground space with probability w. For r independent preparations the probability of no hit is (1−w)^r≤exp(−wr), so r≥log(1/p)/w suffices to reduce that failure event to p. Finite-precision QPE introduces its own failure tails; taking an observed minimum alone is not a rigorous energy certificate because excited states can leak into lower estimates.

If H/λ is block encoded, ordinary qubitized QPE requires precision-sensitive query counts of order λ/εenergy, aside from failure-probability and implementation factors. A small simulation error with only logarithmic cost therefore does not remove the inverse energy-precision factor. All gates implementing each oracle, any state-preparation cost, and any overlap lower bound must be included to assert an end-to-end algorithm.

For a continuum claim, decompose the budget into explicitly bounded effects: finite-volume boundary error, basis/discretization error, omitted or frozen orbital error, Hamiltonian-integral/coefficient error, circuit synthesis/simulation error, and statistical/phase-estimation error. In a fixed finite-dimensional space, ||K−K̃||≤η implies |λmin(K)−λmin(K̃)|≤η by the variational principle. Empirical MP2 sensitivity is not this norm bound. For a compression, the variational upper bound alone gives no certified continuum lower bound or computable convergence rate.

Even accurate energy does not uniformly determine all observables. If a normalized state has energy at most E₀+ε and the rest of the spectrum is at least E₀+g, then its weight outside the ground space is at most ε/g. This elementary spectral inequality requires a positive gap g and addresses closeness to the ground *space*. Degenerate states can have different observables at identical E₀, so “observables of Ψ₀” needs an explicit state-selection convention or a request for ground-space/ensemble data. Unbounded observables additionally need domain/moment control.

## Proposed boundary statement for the main report

**PROVEN (paper proof only):** Exact functional identities, restricted-class representability theorems, finite-model simulation algorithms, and black-box precision lower bounds coexist. None identifies all physically relevant Hamiltonian classes with a poly(N,log(1/ε)) exact solver.

**EMPIRICAL:** Current algorithms improve selected finite-model energies, overlaps, and gate estimates. Error estimates tied to approximate reference methods are not rigorous continuum certificates.

**CONJECTURED/OPEN:** An efficient way to obtain and certify globally adequate ground-state information across the specified isolated point-nucleus Coulomb family, with explicit input-size and continuum-error control. A QMA-hardness reduction for a wider electronic-structure input model cannot silently establish hardness for this narrower family. Likewise, quantum-query lower bounds do not automatically transfer to explicit-coordinate algorithms.

**Sharp open gap exposed by these sources:** A compact representable wavefunction or an exact variational functional is not yet an efficiently discoverable, globally certified continuum ground state. The report should separate representation, optimization, and certification at every step.

## Verification limits and avoided hand-waves

- Did not call a finite active-space energy an exact continuum energy.
- Did not identify LCU PREP with chemical ground-state preparation.
- Did not treat a high symmetry-sector overlap as a lower bound on ground-space overlap.
- Did not infer an efficient optimizer from convexity, exact KS representation, or a proximal convergence theorem.
- Did not infer polylog energy precision from polylog simulation error.
- Did not infer an explicit Coulomb-family complexity lower bound from an oracle theorem.
- Did not infer rigorous integral truncation bounds from MP2 energy tests.
- Did not claim exhaustive coverage or independently verify every proof in every cited paper. The full-text findings above were checked against the indicated sections/statements; sources accessed only at metadata/abstract level are flagged.
