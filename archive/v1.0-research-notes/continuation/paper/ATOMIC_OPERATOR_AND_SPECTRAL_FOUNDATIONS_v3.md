> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Atomic Coulomb operator and spectral foundations

This continuation establishes the shared continuum obligations F02, F03 and F04 in Lean. The result concerns the actual weak Sobolev domain and full fermionic spin space, for every finite electron count. It is a formalization of classical continuum mathematics; no novelty or complete Theorem T claim is made.

## Exact result

Let N be any nonnegative integer and Z any real number. On complex L2 of R^(3N) with 2^N spin components, let F_N be the closed subspace antisymmetric under simultaneous permutation of electron coordinates and spin labels. Define the physical expression

    H = -1/2 Σ_i Δ_i - Z Σ_i 1/|x_i| + Σ_{i<j} 1/|x_i-x_j|.

Its domain is precisely the actual weak H2 space intersected with F_N. The collision representatives used in the definition differ only on proved null sets. The following assertions are proved without a supplied Hamiltonian output, self-adjointness, spectral identification, binding, eigenvector, gap or attainment hypothesis:

1. Every intended H2 input has exactly one L2 Hamiltonian output. That output lies in F_N. The resulting unbounded operator is densely defined, symmetric, closed and self-adjoint on exactly this domain.
2. The actual H1 quadratic form is

       q(ψ) = 1/2 Σ_i ||∇_i ψ||₂² + Σ_spin ∫ V(x)|ψ_spin(x)|² dx.

   Every potential integral is integrable. On H2 this equals Re⟨ψ,Hψ⟩. Actual H2 approximations are dense in the H1 form domain, including all weak first derivatives. The normalized H1 form infimum and original H2 graph infimum are equal.
3. The spectrum is defined by failure of an everywhere-defined bounded two-sided inverse of H-z into the actual operator domain. This definition agrees with mathlib's spectrum when the operator is bounded on the whole Hilbert space. Nonreal points are proved to be resolvent points; reality is not imposed by definition.
4. There is a finite real E equal to both variational infima and to the spectral infimum. It belongs to the actual spectrum and is below every spectral point. It obeys

       -N (max(Z,0))²/2 <= E <= 0.

These are the conclusions of `lean/CoulombSpectralFoundation_v3.lean`, theorem `TheoremT.Continuum.coulomb_shared_continuum_foundation`, source SHA-256 `ffa46294791f8a5082ce2c7e2ed25b63c8129c4d330161a0b2bd1a087396d980`. Its only parameters are N and Z. The definitions `spectralGroundEnergy` and `formGroundEnergy` are separately identified with the original `variationalGroundEnergy`.

A separate verified nonattainment theorem illustrates why the spectral target must not assume a minimizing vector. For N>0 and Z<=0, the spectral bottom is zero, no normalized H1 or H2 minimizer exists, and an actual graph equation Hψ=0 forces ψ=0. This is `CoulombUnboundNonpositive_v1.lean`, SHA-256 `e62f3a252811903c239e8eeed66bad3f19503b21028a51e5e3fd11eb7dae715f`. It makes no assertion about binding at positive Z.

## Main proof dependencies

The graph proof starts with collision nullity, the complex three-dimensional Hardy inequality, compact smooth approximation in the actual weak H1 and H2 spaces, measure-preserving configuration slicing, and spin summation. These give Coulomb multiplication in L2 for every actual H1 input. Weak integration by parts proves the gradient/Laplacian interpolation inequality. The valid coarse multiplier coefficient used in the operator construction is

    C = N(2|Z|+N-1).

For every epsilon>0 the actual scalar and full-spin operators satisfy

    ||Vψ||₂ <= epsilon ||Δψ||₂ + C²/(4epsilon) ||ψ||₂.

The stated continuation specification's smaller multiplier coefficient is being proved separately; no sharper coefficient is silently used in this self-adjointness proof.

The actual weak H2 domain is identified with the L2 distributional Laplacian domain and the quadratic Fourier-weight domain. The positive free resolvent is the literal multiplier

    R_mu = FourierInverse [(2π²|ξ|²+mu)^(-1) Fourier(·)], mu>0.

It maps into actual H2 and solves the free graph equation. Its permutation covariance gives a resolvent on the full fermionic space without an extra spin multiplicity factor. The bounded Coulomb error obeys ||V R_mu||<=C/sqrt(2mu). At mu=1+8C² its norm is below one, yielding surjectivity of H+mu. A proved densely-symmetric real-range criterion establishes actual unbounded self-adjointness.

The spectral proof uses bounded inverses and closed-operator arguments, without assuming a spectral measure. Positive coercivity of a self-adjoint shift gives a bounded two-sided inverse. Conversely, a bounded inverse at a greatest form lower bound would improve that bound, a contradiction. Nonreal shifts have norm bound |Im z| and dense range by the actual adjoint relation, so they are invertible. The original finite graph infimum is identified with the greatest operator form lower bound through normalization of actual graph vectors.

The sharp lower endpoint follows from the weak nuclear inequality

    2t ∫ |f|²/|x_i| <= Σ_k ||∂_(i,k) f||₂² + t²||f||₂², t>=0,

summed at t=max(Z,0), discarding only nonnegative electron repulsion. It assumes no hydrogen spectrum formula. The upper endpoint follows by dilating an explicit nonzero compact smooth fermionic trial. The physical kinetic and potential terms scale as R^(-2) and R^(-1) after normalization, so their energy tends to zero. This proves an infimum bound, not attainment.

The actual H1 derivative graph also has a separately compiled complete Hilbert realization and quantitative shifted-form equivalence. Its squared-form Cauchy completeness is recorded in `logs/hardy/H1_CLOSED_FORM_CHECKPOINT_v1.md`; that final supplementary completeness source was completed after the isolated 145-target snapshot and is not included in the source-rebuild claim below.

## Formal evidence and reproducibility

The declared Lean version is 4.34.0-rc2, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`. Mathlib is pinned to `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. Development used cached pinned dependency objects and preserved prior-audit objects. The final exact source compiled in 31.806 seconds.

The final expanded statement and axiom audit is `audits/formal_semantics/20260910T005419_864596Z/receipt.json`. It covers 29 declarations, including the combined theorem, literal H1 integral form, sharp bounds and nonattainment. All requested axiom reports are present; there are zero printer ellipses. Proof arguments appearing in types are printed, while instance implementations are suppressed. Mathematical definitions and component proof statements are additionally exposed in the linked component audits. Only `propext`, `Classical.choice` and `Quot.sound` occur. There are no added mathematical axioms, `sorryAx`, native verification substitutes, or assumptions of the physical conclusions in the final theorem.

An isolated Linux desktop rebuild has now passed for the exact 145-target source snapshot containing the final theorem and its imported closure. The experiment began with zero copied dependency objects. It rebuilt the pinned package sources, and later bounded segments reused only objects produced inside that same experiment. The four segments took 2,868.943 seconds in total; measured peak container memory was 8,052,625,408 bytes. The final inventory has 4,012 module objects plus two configuration objects. All 145 project targets compiled, source hashes remained unchanged, and all 464 distinct printed project axiom reports use only the three standard foundational axioms.

The complete receipt is `logs/reproduction/remote_source_audit_v6_20260910T010340_582759Z/audit.json`; the sealed summary and exact inventory references are `logs/reproduction/SOURCE_REBUILD_CHECKPOINT_v8.md` and `.json`. The final container stopped with exit zero and no out-of-memory event. A transient monitoring timeout was environmental and did not interrupt compilation. Network and Lake artifact caching were disabled. The pinned compiler and core libraries were reused, not bootstrapped from source. This is a rebuild of the named closure, not all Mathlib or the entire historical nine-target suite; the latter has its separate successful cached rebuild and incomplete resource-bounded source experiment.

To reproduce a development source and strict statement audit locally:

    python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py CoulombSpectralFoundation_v3
    python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/audit_final_statements_v3.py CoulombSpectralFoundation_v3

These commands create fresh timestamped records but reuse dependency objects; they are not substitutes for the isolated source experiment just described.

## Scope beyond these foundations

Full two-electron Theorem T remains unverified. Its original dictionary, rate and bit exponents, physical ground-branch comparison, analytic approximation chain and executable solver have not been composed into a faithful final formal theorem. Reviewed new paper analytic lemmas and separately implemented gap-free atomic/molecular energy procedures retain their own evidence categories. Actual finite rational certificates have been replayed, but those implementations are not Lean-verified and the conservative positive-N arbitrary-precision schedules have not been executed. No numerical reference digits enter the continuum foundation proof.

The next critical formal obligations are the physical hydrogenic/Pauli comparison, existence and separation of the intended two-electron branch, and a continuum residual certificate. Approximate spectral vectors and a domain-correct unbounded Temple theorem are being constructed as new modules. Ground-state regularity, symmetry and physical exponential tails must then connect the reviewed analytic estimates to the original dictionary.

Historical source: `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; frozen `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`. The exact completion criteria are in the preserved `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/CONTINUATION_SPEC_v1.md`. Frozen and previously sealed artifacts remain unchanged; this manuscript supersedes their open-foundation status only for the exact results evidenced above.
