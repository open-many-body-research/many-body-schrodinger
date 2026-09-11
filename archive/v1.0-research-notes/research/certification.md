> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Recent continuum certification claim

Primary source read: Xuefeng Liu, *From estimate to proof: certified ground-state energy bounds for singular Schrödinger operators*, [arXiv:2608.25760v1](https://arxiv.org/html/2608.25760v1), 26 August 2026. Inspected Theorems 1–3, results, and appendices on domain bracketing, projection constants and auxiliary solves.

**UNVERIFIED numerical-certificate claim, with paper arguments:** the preprint reports a whole-space molecular-ion interval `[-0.5514436010,-0.5509672618]`, width approximately `4.76e-4`, using its specified operator convention. Its Neumann/Dirichlet bracketing requires an exterior potential floor above the target eigenvalue. Sharpening requires certified spectral separation and auxiliary estimates. This run has not reproduced those interval computations or independently checked their entire proof chain. The claimed eleven-digit agreement concerns arithmetic evaluation of bounds; it does not mean the displayed interval determines eleven digits of the continuum eigenvalue. No many-electron polynomial total-cost claim follows.

This is relevant progress toward the certification gap, rather than grounds for declaring all continuum certificates absent. The distinction between reported proof, independently reproduced certificate, and Lean proof remains explicit.
