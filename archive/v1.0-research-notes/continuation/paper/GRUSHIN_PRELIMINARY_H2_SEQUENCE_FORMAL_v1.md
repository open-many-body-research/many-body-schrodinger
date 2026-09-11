> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Preliminary local H² for the actual partial regularization sequence

Let Y=KSSpace=R⁴, let T be any finite-dimensional real inner-product space with orthonormal basis (b_j), and let c∈ℝ. Use actual product Lebesgue measure on the ordinary product Y×T. For complex L² classes G,h, assume the actual compact-test weak equation

P_cG=h on Ω,    P_c=−Δ_y−c|y|²Δ_t,

where Ω is open. Let U be open and contained in a compact set C⊆Ω. No first or second derivative of G is assumed.

Take the previously formalized normalized smooth compact kernels K_n on T and the actual L² classes G_n=partialMollifyLp n G and h_n=partialMollifyLp n h. The strongest new theorem, `grushin_partial_regularization_sequence`, proves all of the following for these exact sequences:

- ‖G_n‖₂≤‖G‖₂ and ‖h_n‖₂≤‖h‖₂ for every n.
- G_n→G and h_n→h strongly in product L².
- Eventually n, G_n is locally weak H² on U and P_cG_n=h_n holds for every real C∞ compact test supported in U. The same threshold works for all those tests.

Here local weak H² has an explicit cutoff meaning: for every real C∞ compact χ supported in U, there is an L² representative of χG_n, with genuine first derivative witnesses in every product direction and genuine ordered second derivative witnesses in every pair of product directions, satisfying the compact-test integration-by-parts identities. This is the project's actual `ProductLocalWeakH2On` definition. The ordinary product maximum norm is not mistaken for a Euclidean norm; the local elliptic theorem uses the already proved exact measure transport through WithLp 2.

The new analytic bridge is the full-Laplacian identity. Suppose a product-L² f already has actual first and same-direction second spectator weak derivatives d_j,e_j and satisfies P_cf=h. Twice testing those derivatives against real compact tests gives

Δ_full f = −h + (1−c|y|²)Σ_j e_j

as an actual compact-test identity. For the weighted test (1−c|y|²)φ, the spectator derivatives of its polynomial weight vanish by a proved derivative calculation. The right-hand side is locally L²: the weight is continuous and bounded on every compact set, and h,e_j belong to L². The formal generic local elliptic theorem then supplies every first and ordered second weak derivative of each compact cutoff. No Y derivative or preliminary H² conclusion is assumed in this bridge.

For f=G_n, its d_j and e_j are the previously constructed canonical one- and two-direction spectator jets of the actual convolution. Their L² membership and weak derivative identities were proved directly from compact-kernel fiber differentiation and Fubini. The exact equality `partialMollifyLp_eq_jet_nil` identifies the zeroth jet with G_n. The actual weak equation on U is supplied by partial-convolution commutation and the uniform shifted-test support theorem for C⊆Ω. Thus every premise of the preliminary H² bridge is discharged for sufficiently large n.

Five sources and ten declarations are covered by the combined checkpoint: WeakProductSecondTest_v1, GrushinLaplacianTestRewrite_v1, GrushinSpectatorRegularizedH2_v1, GrushinPartialMollifierH2_v1 and GrushinPartialRegularizationSequence_v1. Exact expanded statements and complete axiom reports are audited; only propext, Classical.choice and Quot.sound occur. Development builds reuse pinned dependency objects. These sources are outside the completed 671-target desktop source-rebuild snapshot, and no isolated rebuild is asserted here.

This result is a fully formalized conditional analytic regularization theorem. The weak equation for the input is an explicit hypothesis; derivative existence for its partial regularizations is a conclusion. The preliminary H² bounds may grow as the kernel narrows. The theorem does not assert that the original G is jointly H² after one Grushin gain, and does not yet pass uniform derivative bounds to G. In particular, it does not resolve the known obstruction to one-step joint H². The next obligation is to derive localized estimates uniform in n and identify their weak limits. Analytic noncomputable integral and representative definitions are not an executable solver, and no rate, bit-complexity, novelty or full Theorem T claim is made.

Frozen original: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. All frozen and successful prior files remain unchanged.
