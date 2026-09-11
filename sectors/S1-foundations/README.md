# S1: Operator-theoretic foundations

**Scope.** For the Coulomb Hamiltonian $H_N$: self-adjointness and domain, semiboundedness, the essential spectrum (HVZ), existence and multiplicity of bound states, and ionization bounds. It also covers the basic definitions every other sector relies on.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| [S1-001](../../claims/cards/S1-001.md) | **Atoms, all N, real Z.** The fermionic Coulomb operator with one nucleus is self-adjoint on exactly the componentwise-$H^2$ antisymmetric domain. The $H^1$-form, $H^2$-variational and spectral ground energies coincide. That common value $E$ is a spectral point, and $-N\max(Z,0)^2/2 \le E \le 0$. The same holds without the symmetry constraint. | L |
| [S1-002](../../claims/cards/S1-002.md) | For $Z \le 0$ and $N \ge 1$: $E = 0$, and there is no zero-energy eigenvector (no bound state). | L |
| [S1-003](../../claims/cards/S1-003.md) | Hydrogen with spin: the ground energy is exactly $-Z^2/2$, with two independent $H^2$ eigenvectors. There is also a kernel-checked sound certificate checker. | L |
| [S1-004](../../claims/cards/S1-004.md) | Hydrogen rank-one (2s-level) comparison $H \ge -\frac{Z^2}{8} - \frac{3Z^2}{8}\lvert g\rangle\langle g\rvert$, on smooth cores and on all of $H^1$. | L |

**Caveats.**
- Only atoms are covered. The multi-center (molecular) operator is not formalized.
- The spectrum is defined inside the project (`TheoremT.OperatorTheory.unboundedSpectrum`: bounded two-sided inverse into the domain), because Mathlib has no spectrum for unbounded operators. The definition looks standard, but an outside Lean expert should review it (S1.1).
- Mathematically, this is Kato (1951). What's new is the formalization.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S1.1 | **Definitions review.** Check that `unboundedSpectrum`, `HasH2`, the weak-derivative graph and the fermionic projector are the standard objects. | A review record under `reviews/S1-002/`, or an erratum. A Lean proof that relates `unboundedSpectrum` to a Mathlib notion would be even better. | open |
| S1.2 | **Molecules.** Extend S1-002 to $M$ fixed nuclei at arbitrary real (or rational) positions. | A Lean theorem with the same shape as `coulomb_shared_continuum_foundation` for a multi-center potential. | open |
| S1.3 | **HVZ, lower half, for helium.** Prove $\inf\sigma_\text{ess}(H_\text{He}) \ge -2$. | A kernel-checked statement on the existing operator. | open |
| S1.4 | **Zhislin for helium.** Prove that $E_\text{He}$ is an eigenvalue below the essential spectrum *without* using the rank-one separator route of S2-002. | Lean | open |
| S1.5 | **Lieb's ionization bound** $N < 2Z+1$ (Lieb 1984) for atoms. | Lean | open |
| S1.6 | **Empty-cache rebuild.** Build the v1.0 Lean library from an empty cache on independent hardware. | A build log and a hash comparison, recorded in `reviews/S1-002/`. | open |

## Where to look

- **Lean sources:** [`lean/Foundation/`](../../lean/Foundation/). Start with `CoulombSpectralFoundation_v3.lean`, `ContinuumFoundation_v1.lean`, `HydrogenSpinGround_v1.lean` and `CoulombUnboundNonpositive_v1.lean`.
- **Statement cards:** `claims/cards/S1-*.md`.
- **Paper blueprint:** [`archive/v1.0-research-notes/continuation/paper/CONTINUUM_FOUNDATIONS_v2.md`](../../archive/v1.0-research-notes/continuation/paper/CONTINUUM_FOUNDATIONS_v2.md).
