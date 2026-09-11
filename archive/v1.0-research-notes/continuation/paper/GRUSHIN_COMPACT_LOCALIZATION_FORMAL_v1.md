> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual compact Grushin localization, v1

For arbitrary finite Euclidean factors Y and T, real c, complex smooth G, and real smooth compact cutoff eta, the actual operator P_c=-Delta_y-c|y|²Delta_t satisfies its exact second-order cutoff commutator. Every derivative is an actual Frechet directional derivative.

Writing E_c(F)=sum_i integral|D_yi F|²+c sum_j integral|y|²|D_tj F|² and C_c(eta,G)=sum_i integral|(D_yi eta)G|²+c sum_j integral|y|²|(D_tj eta)G|², the compiled theorem proves

E_c(eta G)=integral inner_R(eta²G,P_cG)+C_c(eta,G).

The real part of the complex inner product is used, with actual product Lebesgue measure. G need not have compact support. All integrability is proved from the cutoff. Coordinate-weight derivative invariance is discharged, and summing those identities produces the nonsingular |y|² spectator weight.

Young's inequality then gives the actual Caccioppoli estimate

E_c(eta G)<=1/2(integral eta²|G|²+integral eta²|P_cG|²)+C_c(eta,G).

Both identities hold algebraically for every real c. For nonnegative c the energy is nonnegative; unweighted tangential regularity later requires c>0. The present estimates apply to smooth G. Extension to compact weak H² functions and the uniform partial-regularization passage remain obligations.

The checkpoint records exact compiled and expanded statements, standard foundational axioms only, and current source/object hashes. Pinned development objects are reused. These newer localization modules are outside the671-target desktop snapshot. No full Theorem T, analyticity, executable energy approximation, or complexity claim is made.

Frozen commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; frozen RWA_REPORT.md SHA2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066. All work is new continuation source.
