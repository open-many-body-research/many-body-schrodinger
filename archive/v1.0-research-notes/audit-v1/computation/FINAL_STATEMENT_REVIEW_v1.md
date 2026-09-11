> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent semantic review of the new Lean statements

Date: 2026-09-09. This review reads the actual definitions and theorem statements. It does not infer continuum correctness from an axiom list or from agreement between agents. No Lean source was edited by this reviewer.

**Verdict:** the inspected definitions faithfully specify the intended continuum spaces, weak derivatives, Coulomb differential graph, and real two-electron trial dictionary. No finite-dimensional Hamiltonian surrogate, softened Coulomb potential, deliberately empty model, or assumed mathematical structure was found. The difficult domain, spectral, approximation, and algorithmic bridges remain unproved and must not be inferred from the structural lemmas.

The following source versions were read completely:

| New post-freeze path | SHA-256 at semantic review |
|---|---|
| `lean/ContinuumFoundation_v1.lean` | `4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e` |
| `lean/FermionicClosed_v1.lean` | `3eca34b8a832fda95825235e5a4323fc7b79fe628191af5b6e43734acbb946b9` |
| `lean/ExactDictionary_v1.lean` | `9797ece97c2d7e8dcf6e093d76777332e49ab3b1370dedc3af773974d614c959` |

These paths are relative to `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/`. The Lean author confirmed the definitions were stabilized; final proof compilation was still in progress. Therefore final build success, source-to-build hashes, and axiom receipts must be read from the final Lean build records, not inferred from this review. Proof-only changes after these hashes require a source diff; changes to definitions or statements require another semantic review. Earlier failed-attempt logs containing compiler-generated `sorryAx` must not be mistaken for successful final builds.

Historical comparison uses frozen `TWO_ELECTRON_THEOREM.md`, `RATE_DICTIONARY_DECISION.md`, and `rwa_proof/THEOREM_T_COMPOSITION.md`, whose hashes are recorded in `coverage_and_hashes_v1.json`; frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. No frozen bytes were changed.

## Continuum Hilbert space and exchange

`Configuration N` is the real Euclidean space on `Fin N × Fin 3`, hence genuine physical dimension \(3N\). `SpatialL2 N` is the complex \(L^2\) quotient for its Lebesgue volume. `SpinSpace N` is the finite \(\ell^2\) sum over all `Fin N → Fin 2` spin configurations. Its norm sums the spatial squared norms with counting measure on all \(2^N\) spin assignments. These are actual continuum wavefunctions, not arrays of finitely many spatial amplitudes.

The coordinate convention is explicitly \((P_\pi x)_i=x_{\pi(i)}\), and spin is permuted by the same \(\pi\). `pullback π (ψ (permuteSpin π σ))` therefore represents \(\psi(P_\pi x,P_\pi\sigma)\). Requiring this to equal \(\operatorname{sign}(\pi)\psi(x,\sigma)\) is the correct simultaneous space-spin antisymmetry. Whether this pullback is written as a left or right action is immaterial to the defining condition over every permutation; no inconsistent inverse is used between space and spin.

`fermionicSubspace_closed` proves closedness as an intersection of equalizers of continuous maps. With the inherited inner product and completeness this supplies the intended closed fermionic Hilbert space. `fermionic_exchange` is an accessor for the defining antisymmetry condition, not a proof of a spectral property.

## Weak Sobolev domain and Coulomb graph

`WeakPartial` tests the distributional derivative identity against every real smooth compactly supported test function, with complex-valued Bochner integrals. Real tests suffice for complex distributions by testing real and imaginary components. The underlying \(L^2\) representatives are locally integrable; multiplying by a smooth compactly supported test or its derivative is integrable. Thus the totalized integral convention does not make these identities vacuous through nonintegrable integrands. The proved uniqueness theorem explicitly uses the distributional test-function separation theorem.

`HasH2` requires all first derivatives in \(L^2\), and the derivative of every first derivative in every coordinate again in \(L^2\). This is the usual weak \(H^2\) condition, including mixed derivatives. It is not merely twice differentiability away from collisions or an \(H^1\) surrogate. `targetDomain` specifies componentwise \(H^2\) and fermionic membership independently of existence of a Hamiltonian image.

`coulombPotential` has precisely the nuclear term \(-Z\sum_i|x_i|^{-1}\) and one repulsion term for each \(i<j\). Its only convention is Lean's total inverse at zero. Different values on collision sets are physically equivalent only after those sets are proved null; this null-set identification is an outstanding theorem, correctly acknowledged in the source. There is no cutoff or positive softening radius.

`scalarHamiltonianGraph` gives the weak action \(-\frac12\sum_k\partial_k^2f+Vf\), with an \(L^2\) output satisfying the equality almost everywhere. The spin graph additionally requires input and output to be fermionic. The uniqueness proofs show that a graph output, when one exists, is unique. They do **not** prove that every element of `targetDomain` has an output. In particular, the following bridges remain necessary: Hardy control of Coulomb multiplication, existence of the \(L^2\) action on every \(H^2\) input, permutation covariance, graph linearity/density/closedness, symmetry and self-adjointness. Calling this a specified differential graph is accurate; calling it an already verified self-adjoint Coulomb operator would not be.

## Ground energy and possible vacuity

`rayleighNumerator` is the real part of the correctly ordered continuum \(\langle\psi,H\psi\rangle\), summed over spins. `variationalGroundEnergy` takes the infimum over norm-one graph inputs and outputs in `EReal`. Using extended reals is appropriate: it does not force an arbitrary finite answer for an empty or unbounded set.

The present proof collection has not exhibited a nonzero normalized graph trial or proved semiboundedness. It therefore has not excluded \(+\infty\) from an empty numerical range or \(-\infty\) from an unbounded-below range. This is an explicit missing proof boundary, not a discovered false definition. `variational_ground_le_trial` assumes an actual normalized graph trial and then applies the elementary infimum inequality. It cannot prove the existence of such a trial or a finite energy. Equality with \(\inf\operatorname{spec}H\), attainment, the two-electron separator, simplicity and ground-state symmetry remain unproved.

## Exact dictionary and singlet

The native generator has exponent \(Z2^j\), includes the factor \((i+h+k)!^{-1}\), and uses a single diagonal monomial when \(i=h\). The index restrictions \(h\le i\) and \(2j+i+h+k\le n\) are exactly equivalent to the frozen allocation \(0\le j\le\lfloor n/2\rfloor\), polynomial degree at most \(n-2j\). Distances are the physical norms and separation in \(\mathbb R^6\). The nesting and exchange-symmetry statements are faithful.

The definition is the **real** span of real-valued generators, matching the real/rational coefficients used in the frozen algorithm. It is not yet a complex-linear submodule of the physical spin Hilbert space. If one wants the complexified dictionary, its relation to this real span and equality of best residuals need a separate lemma. Such equality is valid at paper level by splitting real quadratic forms, but is not supplied by the current definition alone.

`singlet` has amplitudes \(1/\sqrt2,-1/\sqrt2,0,0\) in the intended up/down configurations. Its formula is correct. `trialDictionary` connects the real function span to genuine \(L^2\) components through almost-everywhere equality with the singlet product. This is an honest lifting relation, not an automatic coercion that invents square integrability. Nevertheless the following facts still need proof: the singlet has norm one and the correct exchange sign, every physical-charge generator has an \(L^2\) lift, the lift belongs to weak \(H^2\), it is fermionic, and the dyadic normalization agrees with a canonical executable basis enumeration. Span invariance under nonzero scaling is elementary but the exact normalization algorithm and bit cost are not formalized.

Allowing all real \(Z\) in structural definitions is harmless. Integrability and the target atomic theorem require the physical restriction, here integer \(Z\ge2\); structural symmetry theorems for arbitrary \(Z\) cannot discharge that restriction. For example, at \(Z=0\) these polynomial generators generally have no nonzero \(L^2\) lifts, and the definitions deliberately do not assert otherwise.

## Final scope

The genuinely useful new formal layer is continuum definitions plus distributional derivative/action uniqueness, closed fermionic structure, and exact real-dictionary symmetry/nesting. Several other lemmas are elementary consequences of their definitions, which is acceptable when reported accurately. No theorem inspected proves continuum self-adjointness, a finite spectral ground energy, normalized dictionary membership, RWA, global approximation, spectral certification, executable rational moments, termination, or bit complexity. The encompassing `noncomputable section` is appropriate for these analytic objects and does not constitute an executable algorithm. A clean final axiom audit cannot change any of these statement-level limitations.
