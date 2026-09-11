> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual physical scaling, KS weak equations and normalized forcing

This formal unit proves the scaled nuclear and two-electron pair KS equations for actual weak H² Coulomb eigenfunctions. It starts from the existing scalar or full fermionic-spin Hamiltonian graph; an eigenfunction is an explicit input, not an asserted existence or uniqueness result.

Let V_Z contain both the negative nuclear attraction and positive electron repulsion, and let g be the continuous representative of a physical eigenfunction. For every ε>0 the new local dilation theorem proves, away from physical collisions,

\[
\Delta(g(\varepsilon x))
 =2\bigl[\varepsilon V_Z(x)-\varepsilon^2 E\bigr]g(\varepsilon x).
\]

The proof establishes nonzero-dilation preservation of the exact collision-free set, the local second-derivative chain rule, and the Laplacian factor ε², and then uses the proved Coulomb homogeneity. The factor ε scales electron repulsion as well as attraction. No new charge-only eigen-equation for g(εx) is assumed.

Write K for the fixed KS map, |K(y)|=|y|². In the N=2 nuclear chart θ_n(y,t)=(K(y),t), and in the pair chart θ_p(y,t)=(t+K(y)/2,t−K(y)/2). Set

\[
P_c=-\Delta_y-c|y|^2\Delta_t,\qquad
u_\varepsilon=g(\varepsilon\theta),\qquad
v_\varepsilon=\varepsilon^{-1}\bigl(g(\varepsilon\theta)-g(0)\bigr).
\]

The nuclear coefficient c is 4; the pair coefficient c is 1. If B_{Z,E} denotes the previously proved unscaled chart potential, the new exact coefficient is

\[
B_\varepsilon=\varepsilon b_\varepsilon,
\qquad b_\varepsilon=B_{Z,\varepsilon E}.
\]

Concretely,

\[
B_{\varepsilon,n}
=-8\varepsilon Z+8|y|^2\left[
\varepsilon\left(-\frac Z{|t|}+\frac1{|K(y)-t|}\right)-\varepsilon^2E\right],
\]

\[
B_{\varepsilon,p}
=4\varepsilon+4|y|^2\left[
-\varepsilon Z\left(\frac1{|t+K(y)/2|}+\frac1{|t-K(y)/2|}\right)-\varepsilon^2E\right].
\]

The formal nuclear definitions and equations also apply to arbitrary finite N and an arbitrary selected electron. The displayed formula specializes them to N=2. The pair theorem retains precisely N=2 and the unscaled physical center t.

The coefficients use the unchanged open chart patches. The nuclear patch excludes the other nuclear and pair collisions; the pair patch excludes the two nuclear zeros. They include the selected fiber y=0 when the other relevant positions remain separated. The coefficients are smooth through that fiber, where their values are −8εZ and +4ε respectively. The exact energy-affine identities are also proved, but this unit supplies no uniform derivative constants.

For every real smooth compact test φ supported in its corresponding patch, Lean proves the actual integrability and weak identities

\[
\int(P_c\phi+B_\varepsilon\phi)u_\varepsilon=0,
\]

\[
\int(P_c\phi+B_\varepsilon\phi)v_\varepsilon
=\int\phi\bigl[-b_\varepsilon g(0)\bigr].
\]

Both sides of the second identity are proved integrable. The source contains no inverse ε. At the selected fiber it is +8Zg(0) in the nuclear chart and −4g(0) in the pair chart.

The homogeneous weak equation comes from the actual classical equation off the fiber, proved integration by parts and continuous codimension-four removability. The inhomogeneous identity follows from the proved constant pairing, subtraction of genuine integrable pairings and cancellation of ε≠0. No derivative of g or of the normalized difference at the collision is assumed. In particular, the generic affine weak implication has its kernel premise discharged by the actual Coulomb weak theorem.

The full-spin weak and difference theorems each construct one simultaneous representative family before quantifying over components, scales, charts and tests. They preserve the common almost-everywhere identity, pointwise simultaneous space/spin fermionic permutation law and inherited spin square-sum bound. The scalar results apply to every continuous representative satisfying the actual almost-everywhere identity, so the equations may be used for a representative already selected elsewhere in the project.

The unit comprises nine new modules and 28 declarations: six physical scaling/KS/wrapper modules (13 declarations), two coefficient modules (12 declarations), and one affine weak-forcing module (3 declarations). Exact statements compile under the pinned Lean environment; four strict v5 receipts have complete axiom reports, no ellipses and only propext, Classical.choice and Quot.sound. The companion checkpoint binds all source/object hashes, development checks, expanded logs and focused review. Existing dependency objects were reused; this unit is not an isolated source rebuild.

This completes the assigned actual ε-scaled equations and normalized-difference forcing portion of the reduced R01/R03 path. The simultaneous nuclear-pair origin remains outside these chart patches. Uniform local estimates, all-order factorial estimates, collision-chart descent, global dictionary approximation, implementation correctness and full Theorem T remain separate obligations. The next integration uses the existing local Lipschitz amplitude bounds and independently proved uniform finite coefficient/source bounds in the local Grushin gain theorem.

Frozen historical source: `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`, SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Frozen artifacts and all earlier successful source and receipt bytes remain unchanged.
