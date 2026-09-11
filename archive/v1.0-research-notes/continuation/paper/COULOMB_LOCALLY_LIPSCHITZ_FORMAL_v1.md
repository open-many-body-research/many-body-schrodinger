> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Coulomb eigenfunctions: pointwise representatives through all collisions

Evidence category: fully formalized regularity theorems, compiled in the pinned Lean environment with expanded-statement and axiom audits. This result supplies necessary physical regularity for the original two-electron program; it does not complete Theorem T.

For finite N≥1 and real Z, consider the actual scalar operator

H = −(1/2)ΣᵢΔᵢ − ZΣᵢ|xᵢ|⁻¹ + Σᵢ<ⱼ|xᵢ−xⱼ|⁻¹

on the weak Sobolev H² domain in L²(R^(3N);C). Let f be an actual domain eigenfunction at a real energy E. The theorem `scalar_coulomb_unique_locally_lipschitz_representative` proves the existence of exactly one locally Lipschitz function u on all of R^(3N) representing f almost everywhere. This uniqueness concerns the representative of the specified L² vector. It does not assert uniqueness of an eigenvector or eigenspace.

The theorem `scalar_coulomb_bounded_locally_lipschitz_representative` retains the previously formal Moser bound pointwise:

|u(x)| ≤ M(N,Z,E) ||f||₂ for every x.

M is the exact finite coefficient `coulombMoserBoundCoefficient` defined in the preceding boundedness development. Its Sobolev coefficient remains an unevaluated mathematical quantity. The local Lipschitz constants in this result are existential; no efficient evaluation of them is claimed.

For the full fermionic spin space, `coulomb_spin_locally_lipschitz_representative` supplies locally Lipschitz component representatives uσ with simultaneous spatial/spin antisymmetry at every point:

u_(σ∘π)(permuteSpace π x) = sign(π) uσ(x).

The square-sum amplitude obeys

(Σσ|uσ(x)|²)^(1/2) ≤ M(N,Z,E)||ψ||₂.

There is no multiplier 2^N in this amplitude estimate. The theorem uses the actual full fermionic Hamiltonian graph and does not assume binding, isolation, a ground state, or pre-existing bounded derivatives. Its eigenfunction hypothesis is an actual operator equation, not a premise asserting regularity.

The domain of every representative is the whole configuration space. Thus these statements include nuclear collisions, pair collisions, disjoint collisions, triples away from the nucleus, and intersections of all these strata. They do not assert analyticity at such points.

## Proof chain

Set F = −ZΣᵢ|xᵢ| + (1/2)Σᵢ<ⱼ|xᵢ−xⱼ|. Earlier formalized weak identities give ΔF=2V and genuine localized H² product jets. On an interior ball, the actual transform g=exp(−F)f satisfies

Δg = −2∇F·∇g − (|∇F|²+2E)g.

The coefficients are globally bounded, and the previously proved global essential bound for f supplies local essential boundedness of g. This transformation includes collision sets distributionally.

The normalized Newton fundamental solution and its gradient were constructed and proved distributionally in dimension d=3N. Actual H² mollification and strong L² convergence identify a compactly supported weak first derivative with the truncated Newton-gradient convolution of the weak Laplacian. Young and Hölder inequalities then give interior integrability gains. Every convolution integral required for the finite Young gain is proved to exist almost everywhere.

The implemented proof iterates κ=2d/(2d−1), qⱼ=2d/(d−j), starting at q₀=2 and ending at q_(d−1)=2d. Cutoffs transfer bounds from a ball of radius 4A to one of radius A. The bounded-coefficient equation supplies the Laplacian integrability at each step. The conjugate-exponent endpoint then proves that all genuine weak first derivatives of g are locally L∞. These intermediate premises are discharged by the finite induction.

For the representative step, compact localization produces an actual L² weak Sobolev function with globally bounded weak first derivatives. Its normalized mollifications have a uniform Lipschitz constant, using their exact differentiated convolution formulas and the coordinate bound for the Fréchet derivative. Almost-everywhere pointwise convergence gives a Lipschitz function on the convergence set. Real and imaginary Lipschitz extensions give a global representative, with an allowed factor two in the extension constant.

The finite distance sum F is locally Lipschitz, so multiplication by exp(F) restores a locally Lipschitz representative of f on each ball. Continuity and positivity of Lebesgue measure on nonempty open sets prove pointwise compatibility on overlaps. A countable open cover then gives the global representative. The same continuity argument upgrades the essential amplitude estimate and quotient symmetries to pointwise statements.

## Actual two-electron ground state

For Z≥2, `twoElectron_physical_pointwise_ground_with_H2_decay` constructs one actual normalized H² scalar ground vector at the already spectrally identified full fermionic ground energy, together with its bounded locally Lipschitz representative. The representative is real, exchange invariant, and invariant under simultaneous orthogonal transformations, pointwise. The same vector has genuine weak first/second derivatives and the established full H² exterior estimate

weakH2ExteriorNorm(f,d,e,r) ≤ C exp(−a r), whenever a≥0 and a²<Z²/112.

No strict pointwise positivity or normalization by a selected point value is asserted. The ground-state existence, spectral comparison and tail bounds come from their earlier formal proofs, rather than being new assumptions in this composition.

## Evidence and remaining boundary

The exact sources and strict receipts are recorded in `../audits/COULOMB_LOCALLY_LIPSCHITZ_CHECKPOINT_v1.json`. Only `propext`, `Classical.choice`, and `Quot.sound` occur where needed. The development reuses pinned dependency objects. The sources in this checkpoint are newer than the 392-target Colab rebuild snapshot, so that run cannot verify them. No independent agent review of this new chain was available because the proof agents had reached their usage limit.

This is a regularity theorem, not an executable approximation algorithm. Classical selection of representatives does not provide a finite wavefunction representation. Uniform analytic estimates, weak KS pullbacks, factorial recurrence, quantitative descent, the unchanged global trial dictionary, acceptance/termination, and operational complexity remain separate formal obligations. Full Theorem T and an arbitrary-precision two-electron certificate producer remain unverified.

The primary classical comparison is Fournais, M. Hoffmann-Ostenhof, T. Hoffmann-Ostenhof and Sørensen, [Sharp regularity results for many-electron wave functions](https://arxiv.org/pdf/math-ph/0312060), inspected in its 2003 version. That paper proves stronger classical regularity after additional factors; this continuation makes no mathematical novelty claim for local Lipschitz regularity. Its kinetic convention is −Δ, so its factor coefficients cannot be copied directly into the present −(1/2)Δ model.

Frozen provenance is preserved: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The frozen `RWA_REPORT.md` has SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`; frozen `rwa_proof/RWA_THEOREM.md` has SHA-256 `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`. Their containing directory is `THEOREM_T_FREEZE_2026-09-09_212604/`. This continuation changes none of those bytes or the original dictionary.
