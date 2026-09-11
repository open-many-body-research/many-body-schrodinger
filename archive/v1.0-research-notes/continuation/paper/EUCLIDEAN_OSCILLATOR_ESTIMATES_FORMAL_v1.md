> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Euclidean oscillator estimates, version 1

Evidence: Lean kernel compilation and complete expanded-statement/axiom audits, indexed by `audits/EUCLIDEAN_OSCILLATOR_ESTIMATES_CHECKPOINT_v1.json`. Only propext, Classical.choice and Quot.sound occur. No additional mathematical axioms, native computation, or assumed oscillator estimate is used.

Let ι be any finite index type, d=card ι, with actual Euclidean space R^ι, Lebesgue volume and its standard orthonormal coordinate vectors. For a real a define the actual differential expression

A_a u = -sum_k D_k(D_k u) + a² |x|² u.

For every compactly supported C¹ complex u,

d a integral |u|² <= integral sum_k |D_k u|² + a² integral |x|² |u|².

For compactly supported smooth complex u, actual integration by parts identifies the right side with integral Re(conj(u) A_a u). Actual L² Cauchy–Schwarz, with the integral explicitly identified with the L² quotient norm, gives

d a ||u||₂ <= ||A_a u||₂.

For a>=0 the theorem without any extra integrability premises is

(d a)² integral |u|² <= integral |A_a u|².

Compact support and continuity discharge every integrability and MemLp requirement. The norm formulation has explicit MemLp inputs used only to construct the actual quotient objects; the final squared-integral formulation derives them and has none of these premises. Smoothness is C∞, not analyticity. Finite empty ι and a=0 are allowed. No spectral identification of the oscillator is assumed or claimed.

The proof first establishes, for any real continuous linear functional L and v with L(v)=1 and real compact C¹ u,

integral (D_v u + a L u)² = integral (D_v u)² + a² integral (L u)² - a integral u².

It uses the zero integral of D_v(L u²). Real and imaginary parts yield the complex inequality; summing the actual Euclidean coordinates yields the d factor. All integrals are actual Lebesgue integrals, with integrability supplied before linearity steps.

This is the oscillator estimate required for the frozen Grushin argument's Fourier fibers (d=4). Partial Fourier transformation of the actual lifted operator, its normalization factors, cross-term estimates, local weak regularity gain, quantitative initialization and factorial recurrence remain separate open formal obligations. The Coulomb equation, trial dictionary, n schedule and physical ground target have not been altered. Full Theorem T remains unverified. No novelty claim is made for this standard oscillator estimate.

Development reused pinned Lean4.34.0-rc2/Mathlib dependency objects; the exact pins and source/object hashes are in the receipts. The prior250-target desktop source rebuild remains separately sealed. Colab v13 stopped at its3h cap with2434 completed compiler calls, none failed, and no392project targets completed; its runtime files were subsequently lost. The v15 snapshot has632targets and includes the form-bound chain, but was taken before the operator and norm modules and does not cover those modules. The v15 source rebuild has not yet started at this checkpoint.

Frozen provenance: `THEOREM_T_FREEZE_2026-09-09_212604`, commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tagtheorem-t-proof-freeze-2026-09-09. Frozen `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` SHA2565d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c. The frozen source is preserved verbatim; this is a new continuation result.
