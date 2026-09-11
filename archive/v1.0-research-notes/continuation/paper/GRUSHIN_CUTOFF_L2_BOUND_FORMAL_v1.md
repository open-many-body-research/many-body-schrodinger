> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Grushin cutoff error bound

For finite Euclidean factors Y and T, real c, a real smooth compact cutoff η and any actual complex product-Lebesgue L² class f, the cutoff energy equals ∫W|f|², where W=Σᵢ|D_yᵢη|²+c|y|²Σⱼ|D_tⱼη|². Every term is genuinely integrable; no smoothness or boundedness of f is assumed.

The Lean proof establishes W≤C ⇒ cutoffEnergy≤C‖f‖², and supplies a finite C≥0 for every fixed cutoff, uniformly over all L² inputs. For c≥0, if the squared Y and T derivative sums are bounded by A² and B² and |y|≤R on the cutoff support, it proves the explicit coefficient C=A²+cR²B². Derivatives vanish outside the support, including at points where no smoothness premise is needed for that support lemma.

These are fully formal mathematical estimates on the actual L² quotient. The coefficient hypotheses are explicit geometric cutoff bounds, not an assumed derivative estimate on the unknown. The automatically selected finite bound is analytic existence, not an executable constant-selection algorithm. The results do not alone establish uniform local Grushin regularity, joint H², analyticity, or Theorem T.

Two modules and ten declarations passed expanded-statement and complete axiom audits (20260910T173108_355275Z), using only propext, Classical.choice and Quot.sound. Pinned development objects were reused. These sources are outside the sealed v18 and dispatched v19 source-rebuild snapshots. Failed development elaborations remain in separate logs; only successful final source hashes are accepted.

Preservation anchor: frozen rwa_proof/RWA_THEOREM.md, SHA-256 d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09; commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09. Frozen bytes are unchanged. Next: uniform local weak Grushin energy and commutator composition, followed by genuine weak-derivative limit passage.
