> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of exterior coercivity and decay

Reviewed paper: `COULOMB_EXTERIOR_COERCIVITY_DECAY_v1.md`, SHA-256 `2e93a83eb90462696ce1a6f9d318ce63610ff9a74bd622822129c4d32c5ddc1e`.
Evidence is a paper implication with explicit physical operator hypotheses, not Lean verification.

The bounded saturation L(1-exp(-rho/L)) is increasing to rho. For each finite L, the cutoff kills a neighborhood of the radial singularity and the resulting weight and its square have bounded first and second weak derivatives. Thus both weighted test vectors lie in the actual H2 domain. The weighted eigenfunction identity requires no D(H²). The squared-sum estimate costs precisely one alpha²||v||² after the kinetic factor1/2; choosing alpha²=delta0/2 leaves the stated positive half of exterior coercivity. The cutoff annulus term is bounded independently of L. Fatou or monotone convergence therefore gives the claimed weighted L2 estimate with the displayed constant.

The radial L2 bound is inserted into the previously reviewed radial H2 tail estimate before changing coordinates to S=sum|xi|. This yields the single factor1/sqrt(N), not two. The small-radius global graph bound has the correct exp(3alpha) reserve. All spin components share the scalar cutoff and the same constants.

The hydrogenic application keeps the actual rank-one comparison and the actual eigenvalue's trial upper bound explicit. For an exterior vector, Cauchy-Schwarz reduces the rank-one defect to the tail of the explicit normalized product trial. Its gamma density has shape6 and rate2Z; the convolution coefficient and five integrations by parts give exactly exp(-2ZR) times the degree5 exponential partial sum. At 2ZR=10 the rational degree13 lower partial sum proves the strict1/12 bound without floating-point exponential values. The algebra gives Z(11Z-20)/32>=Z(3Z-5)/16 for Z>=2, with equality in that final comparison at Z=2.

No error was found. The complement input is a discrete-level form comparison on the full relevant domain. It is not an ionization threshold used as an excited-state separator. Existence, hydrogenic complement control and the trial integral remain separate physical obligations; this theorem derives the physical exponential tail once they are supplied.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; exact frozen target hashes are recorded in the source. Previous sealed results remain unchanged.
