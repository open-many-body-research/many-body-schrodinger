> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of global eigenfunction boundedness

Reviewed source: `COULOMB_GLOBAL_BOUNDEDNESS_v1.md`, SHA-256
`d103aa471fcb626ca330d02a4cfbc6534a038e8827e129cff6c24ef3351377a7`.
Evidence: independently reviewed paper proof, not a Lean theorem.

The product-integration induction proves the required W1,1 estimate, and the power alpha=2(d-1)/(d-2) gives exactly the stated Sobolev constant 4d(d-1)^2/(d-2)^2. The extension uses actual H1 approximation and identifies the stronger-norm limit with the original L2 limit. It makes no finite-measure assumption.

The nonlinear tests are truncated before being used. At every finite truncation the maps are Lipschitz and vanish at zero, hence lie in H1. The actual H2 equation extends to these tests because both the Laplacian and Coulomb output lie in L2. The phase contribution in the complex gradient computation is nonnegative; the displayed radial expression is correctly an inequality, not an equality for arbitrary complex functions. On the truncation level the usual weak chain-rule convention is harmless. The pair potential is dropped only with its actual positive sign.

The Hardy/Young absorption coefficient is valid for every real iteration exponent p>=2: 2|E|/c_p<=p^2|E| and a^2/c_p^2<=a^2p^2. Monotone convergence then establishes the next Lp integrability, so no high-power integrability is assumed circularly. The two exact geometric sums yield the stated infinite-product constant. The argument from bounded Lp norms to essential boundedness restricts to a finite positive-measure superlevel set provided by initial L2 integrability; it is valid on the infinite configuration space.

The constant is uniform over spin components. Summing their squared pointwise estimates gives the full pointwise spin-norm bound with no factor 2^N. No positivity or eigenvalue simplicity is required. N>=1 is essential to the displayed d>=3 Sobolev iteration and is stated explicitly.

No error was found. This removes the L-infinity premise in the reviewed exterior analytic theorem when an actual scalar H2 eigenfunction is available. It proves neither eigenfunction existence nor rotational invariance, binding, local Lipschitz regularity, exponential tail existence or any computational claim. The cited classical source is attribution only; its inaccessible full text is not used as a proof premise.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The exact frozen downstream target and hashes are recorded in the reviewed source. No frozen or sealed artifact was changed.
