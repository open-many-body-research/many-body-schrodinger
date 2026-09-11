> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual partial Fourier foundations, version 1

For complex-valued smooth compactly supported G on Y x T, with T a finite-dimensional real inner-product space, define F_T G(y,xi) = integral exp(-2 pi i <t,xi>) G(y,t) dt. This is exactly the pinned Mathlib Fourier transform, with its 2 pi normalization.

The following are kernel-verified:

* Each fixed-frequency fiber is smooth and compactly supported in Y. The support is contained in the projection of the original compact support. Smoothness follows from a proved Banach-valued differentiation-under-integral theorem, with the dominating functions constructed from compact support; all finite derivative orders are covered.
* Every actual Y-directional derivative commutes with F_T. Every actual T-directional derivative becomes multiplication by 2 pi i <xi,v>; a repeated derivative gives -(2 pi)^2 <xi,v>^2.
* Each fixed-Y slice satisfies Plancherel and belongs to every Lp after Fourier transformation.
* For Y also a finite-dimensional real inner-product space, the joint transformed squared norm is integrable and

      integral_xi integral_y |F_T G(y,xi)|^2 = integral_(y,t) |G(y,t)|^2.

  Both measurability and Fubini integrability are proved. The measure on the right is explicitly the product of the Euclidean volume measures.
* Negation, finite sums, addition, and multiplication by a coefficient depending only on Y have their exact integral identities.

The generic compact partial-integration smoothness theorem allows Banach-valued outputs, with Y and the output in the same Lean universe to permit induction through derivative spaces. All concrete Euclidean and complex spaces used here satisfy that condition. This is a type-level constraint, not an analytic hypothesis.

Evidence: thirteen source modules, forty-eight declarations, complete expanded statements and axiom reports. Only propext, Classical.choice, and Quot.sound occur. Existing pinned development objects were reused; these sources are outside the prepared 632-source Colab rebuild snapshot. No isolated source rebuild of this checkpoint is claimed.

Next: identify the actual transformed Grushin operator with the oscillator and transfer the verified fiber estimates. Weak-solution regularity, analytic/factorial estimates, and full Theorem T remain open. This checkpoint makes no novelty claim.

Frozen provenance: THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md, SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c; commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09. Frozen artifacts are unchanged.
