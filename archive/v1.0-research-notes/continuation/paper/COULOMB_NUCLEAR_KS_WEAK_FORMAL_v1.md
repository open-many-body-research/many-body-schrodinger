> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# The actual nuclear KS weak equation on its coefficient patch

Evidence: Lean-verified mathematical results in the pinned development environment. This is a local transformation theorem for actual continuum eigenfunctions, not an analytic regularity theorem or a numerical algorithm.

For finite N≥1 and real Z,E, let f be an actual weak H² eigenfunction of the scalar repulsive Coulomb Hamiltonian H=−½ΣΔ_i−ZΣ|x_i|⁻¹+Σ_{i<j}|x_i−x_j|⁻¹. The proved regularity theorem supplies one globally locally Lipschitz representative g of f. For each electron i, retain all 3(N−1) spectator coordinates s and define θ_i(y,s) by inserting the actual quadratic KS map K(y) into its spatial position. Set U_i=g∘θ_i on R⁴×R^{3(N−1)}.

Let Ω_i consist exactly of configurations in the lifted coordinates where every other nuclear position is nonzero and every pair of distinct electron positions is unequal. The selected position may vanish. This is a proved open set. Write V_i for the Coulomb potential with only the selected nuclear attraction removed and put

B_i(y,s)=−8Z+8|y|²(V_i(θ_i(y,s))−E).

The coefficient B_i is real analytic at every point of Ω_i, including y=0, where its value is −8Z. For every real smooth compactly supported test φ with tsupport φ⊆Ω_i, the following integrand is actually integrable, and

∫ [−Δ_yφ−4|y|²Δ_sφ+B_iφ] U_i = 0.

All derivatives in the Lean statement are actual Fréchet derivatives in the coordinate bases. All spectator second derivatives occur. Integrals use ordinary product Lebesgue measure, whose Haar property is proved. The conclusion does not use a totalized nonintegrable integral.

For the full fermionic spin Hamiltonian on its actual weak H² domain, one family of representatives u_σ has this conclusion for every σ and every selected i simultaneously. The same family is globally locally Lipschitz, represents the actual L² spin vector almost everywhere, and satisfies pointwise simultaneous spatial-and-spin antisymmetry. The earlier square-sum amplitude bound is retained with no factor 2^N. Existence of an eigenfunction is an explicit input; neither binding nor a unique eigenvector is assumed or inferred.

The proof first identifies the actual classical PDE away from collisions using the verified all-order elliptic bootstrap, Fourier moments, inversion and weak-jet identification. The exact KS chain rule then proves the classical lifted equation away from y=0. Local integration by parts transfers its derivatives onto tests. The weight |y|² is constant in spectator directions, which yields the exact weighted identity. The codimension-four smooth-hole argument then removes y=0: its second-derivative cutoff defect has order δ⁻² and support with volume of order δ⁴, so its integral against the locally bounded continuous pullback vanishes. A compact cutoff extends the coefficient only for each test; equality on the test support transfers the result back to B_i. Thus no global continuity at the other Coulomb collisions is presumed.

The analytic coefficient proof uses genuine order-ω differentiability of the polynomial lift, the nonvanishing norms on the stated patch, and inversion. It does not infer analyticity from C∞ regularity. It currently supplies qualitative analyticity, without numerical radii, derivative constants or uniformity in a rescaling parameter.

The selected chart excludes simultaneous other nuclear collisions, pair collisions and their intersections. One such map does not clear those strata. Solution analyticity, quantitative H¹² initialization, factorial estimates, coordinate descent and the original dictionary approximation remain separate obligations. Full Theorem T remains unverified.

Build and expanded-statement/axiom receipts are indexed by `../audits/COULOMB_NUCLEAR_KS_WEAK_CHECKPOINT_v1.json`. Only propext, Classical.choice and Quot.sound occur in the audited final dependency reports. No sorry, sorryAx, native_decide or added mathematical axioms are accepted. Pinned library and prior continuation objects were reused. This new chain is outside the 392-target Colab rebuild snapshot; that remote run's final state remains unobserved. There is no independent agent review of this chain because agent usage quota is exhausted.

Frozen provenance: `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`, SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`; commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The frozen nuclear normalization is recovered at physical scale one. General scale-uniform conclusions have not been inferred from this theorem. No novelty claim is made.
