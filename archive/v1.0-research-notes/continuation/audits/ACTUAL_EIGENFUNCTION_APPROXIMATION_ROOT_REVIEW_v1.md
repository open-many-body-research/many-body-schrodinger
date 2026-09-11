> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of actual-state RWA and dictionary approximation

Reviewed paper: `ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md`, SHA-256 `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696`.
This is a composed paper theorem. Its analytic component proofs and the Lipschitz proof have separately recorded independent reviews. No Lean approximation or algorithm theorem is asserted.

Actual H2 plus the distributional equation gives the actual L2 eigenfunction identity by the proved Hardy multiplier. The global boundedness and local Lipschitz results then apply without circular analytic premises. Rotation invariance of the Sobolev class becomes invariance of the unique continuous representative: for each fixed rotation, a continuous difference vanishing almost everywhere vanishes everywhere. Local G1 and exterior G2 retain exactly their physical coordinates and shared neighborhoods.

For the extracted remainder, the polynomial T=r²+s² is bounded away from zero on the organizing simplex. A complex perimetric displacement at radius1/128 changes T by at most8h+8h², so it stays in one right-half-plane logarithm branch. The bounds |f|<=4Z+1, |q|<=6, |Log T|<4 and epsilon|log epsilon|<=1/e give the displayed O(epsilon) amplitude, including30|kappa|. Cauchy's formula and S_per<=S_phys<=2S_per give the exact physical weight1 derivative bound. I checked the original frozen RWA formula: kappa_Z=Z(2-pi)/(3pi) and the function exp(-f)psi-kappa_Z psi0 q log T agree literally.

The proof correctly exposes an important limit: this weighted RWA estimate holds for any finite kappa. It cannot identify the correct Fock coefficient or prove a stronger extraction regularity claim. The original coefficient's independent mathematical role remains an obligation.

With the additional actual exponential L2 tail, exchange symmetry and normalization, the reviewed tail transfer supplies full physical H2 G3. Together with the derived G1/G2 these discharge the explicit hypotheses of the previously reviewed endpoint dictionary theorem. The resulting exp(-c n^(1/3)) existence rate is for exactly the original e^(-Z2^j S) symmetric polynomial dictionary and its original degree schedule. The unit singlet lift preserves the full physical fermionic H2 norm.

No error was found in this composition. Actual eigenfunction existence, the stated rotation/exchange symmetry, and the exponential tail remain its physical inputs; the newly reviewed exterior-coercivity theorem offers a separate route to the tail. There is still no executable selection of the psi-dependent coefficients, verified finite solver, continuum energy certificate implementation or full Theorem T claim.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Frozen relative paths and SHA-256 values are explicit in the reviewed source, and all successful prior artifacts are preserved.
