> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Evaluated constants for the unchanged smooth transition

Evidence: Lean compilation and strict v6 statement/axiom audit, seventeen declarations; standard foundational axioms only. Pinned development objects reused, outside the v20 source rebuild snapshot.

Let g(x)=expNegInvGlue(x), d(x)=g(x)+g(1-x), and T(x)=g(x)/d(x)=Real.smoothTransition(x). These are the existing Mathlib functions, including their globally smooth flat junctions.

The positive exponential series gives u^n exp(-u)≤n! for u≥0. The exact global derivative identities g′(x)=(x⁻¹)^2g(x) and g″(x)=((x⁻¹)^4−2(x⁻¹)^3)g(x) therefore imply |g′|≤2 and |g″|≤36. The nonpositive half-line is handled by the genuine global derivative formulas and g=0 there. Since either x or1−x is at least1/2, monotonicity gives d≥g(1/2)=exp(-2)≥1/16; the last bound follows from exp(1)<3.

Consequently |d′|≤4 and |d″|≤72. Differentiate the exact identity dT=g, using 0≤T≤1. It gives d|T′|≤2+4=6, so |T′|≤96. Differentiate again: dT″=g″−d″T−2d′T′. Thus d|T″|≤36+72+2·4·96=876, giving |T″|≤14016.

Both evaluated bounds are universal in x. They instantiate the previously proved C-infinity cutoff geometry directly. They are conservative and do not assert the smaller constants from the separate piecewise-quintic paper construction. No trial dictionary, Hamiltonian, domain or physical coordinate was changed.

The coefficients and physical Lipschitz amplitudes retain their own explicit dependencies; evaluating these two cutoff constants does not evaluate every analytic constant or prove H12 by itself. Next: compose the genuine physical finite reserve and continue the all-order factorial chain.
