> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of the actual complex coefficient bounds

Reviewed source: `COULOMB_COMPLEX_COEFFICIENT_BOUNDS_v1.md`, SHA-256
`a6b9361f229a29e3df2cf0e3e20552da7cfeb49dfbbf7f8f15d0112375eaa5b5`.
Evidence: independent mathematical review of a paper proof, not Lean verification.

The inverse-distance construction uses the holomorphic polynomial sum of coordinate squares. The complex Euclidean norm appears only in estimates. The relative perturbation is at most 17/64, so the binomial branch stays in one disc excluding zero. The resulting bound 8/sqrt(47) times the inverse real separation is valid. Thus neither an implicit Hermitian continuation nor a branch-cut passage occurs.

The nuclear displacement bounds sqrt(3)/32 and 9sqrt(3)/256, and the pair bound 17sqrt(3)/512, are each within 1/8. The complex KS polynomial estimate uses its component coefficients rather than the real norm identity. Multiplying the two bounded inverse nuclear terms by the actual pair coefficient gives Z/16; the nuclear chart gives (Z+1)/16. Both energy coefficients and the kinetic factors c=4 and c=1 match the independently reviewed lifted equations. Cauchy margin h/2 gives the declared factor 64 at every order.

The source is the actual normalized difference source -a0 times B/epsilon. Its norm uses the finite outer-box volume. The physical chart images have norm less than 2epsilon, so the declared common physical ball controls the pullback amplitude. The Cartesian pair displacement uses twice the individual displacement and is included in the stated radius. No unknown derivative of the solution is hidden in a coefficient constant.

No error was found in these arguments. This discharges only the coefficient and source-neighborhood input to the paper analytic lemmas. The actual solution, its Lipschitz regularity, symmetry and spectral role are distinct obligations.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; exact frozen source paths and hashes are recorded in the reviewed source. No frozen or sealed file was changed.
