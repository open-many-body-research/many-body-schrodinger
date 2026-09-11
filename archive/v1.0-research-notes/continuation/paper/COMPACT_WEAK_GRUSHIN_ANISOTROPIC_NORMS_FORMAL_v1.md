> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact weak directional interpolation and anisotropic Grushin norms

For actual complex Lebesgue L² classes f,d,e in any finite real Euclidean space, with compact AE support of f and actual weak directional derivatives D_v f=d and D_v d=e, Lean proves ‖d‖²=−Re〈f,e〉 and therefore ‖d‖²≤‖f‖‖e‖≤(‖f‖²+‖e‖²)/2. No other weak derivative is required. The proof uses actual mollification of this two-link weak chain, the compact support of the mollified f, smooth integration by parts, and strong L² limits. The product result transports through the actual measure-preserving WithLp 2 map and returns to ordinary product Lebesgue L².

For Y=R⁴, any finite Euclidean spectator space, and c>0, a compact actual weak H² input u satisfying P_c u=H against all real smooth compact tests has the three separate bounds:

- Σᵢ‖D_yᵢu‖² ≤ 2‖u‖²+(3/4)‖H‖².
- Σⱼ‖D_tⱼu‖² ≤ ‖H‖²/(16c).
- ΣᵢΣⱼ‖D_yⱼD_yᵢu‖² ≤ (3/2)‖H‖².

The second and third follow from the previously proved actual compact weak Grushin estimates, dropping only nonnegative terms. The first sums four directional interpolation inequalities and bounds the diagonal Hessian sum by the full ordered Hessian sum. The constants therefore have no spectator-dimension factor. Full H² of u is an explicit input premise, to be supplied by the separate partial-regularization/localization proof. The theorem does not infer full H² for the original weak Grushin solution and does not bound unweighted TT derivatives.

Three modules/seven declarations passed strict expanded statement and complete axiom audits 20260910T173708_913021Z and 20260910T174037_340657Z, with only propext, Classical.choice and Quot.sound. Pinned development objects were reused. These modules are outside v19. This is mathematical formalization, not a numerical algorithm or novelty claim.

Preservation anchor: frozen rwa_proof/RWA_THEOREM.md SHA d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09, commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Next: combine uniform localized output bounds with actual anisotropic bounded weak limits. Full Theorem T remains unverified.
