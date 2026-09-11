> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Euclidean oscillator component estimates, version 1

For every finite dimension d, complex-valued compactly supported smooth u on the actual Euclidean space, and a >= 0, put A_a u = -Delta u + a^2 |x|^2 u. Lebesgue integration and genuine Frechet directional derivatives are used. The compiled results establish

    d ( integral |Delta u|^2 + a^4 integral |x|^4 |u|^2 )
        <= (d+2) integral |A_a u|^2,
    2 d a^2 integral |x|^2 sum_k |D_k u|^2
        <= (d+2) integral |A_a u|^2.

No division by d is used; the general statements include d=0. In d=4 they give the coefficient 3/2 in each component estimate. This verifies the oscillator-fiber constant used in the frozen Grushin argument.

The mathematical addition is the actual integration-by-parts identity

    integral inner_R(-Delta u, |x|^2 u)
      = integral |x|^2 sum_k |D_k u|^2 - d integral |u|^2,

and its squared-operator-norm consequence. The directional precursor permits any real continuous linear functional L and direction v, with correction (L v)^2. All required integrability is proved from smoothness and compact support. The preceding oscillator lower estimate absorbs the negative term in the squared norm expansion.

Evidence: five modules and thirteen declarations compile with complete expanded statements and axiom audits, as recorded in the accompanying checkpoint. Only propext, Classical.choice, and Quot.sound occur. Pinned development object caches were reused. These five modules are outside the prepared 632-source Colab snapshot, and no isolated rebuild of them is claimed.

The partial Fourier transfer to a full Grushin estimate, weak local regularity, quantitative initialization, factorial estimates, solution analyticity, and full Theorem T remain separate obligations. The next proof uses the fact that Fourier transformation only in spectator variables preserves compact support in the remaining coordinates. No novelty is asserted.

Frozen provenance: THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md, SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c; commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09. Frozen bytes remain unchanged.
