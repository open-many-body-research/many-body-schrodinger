> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak H² Grushin energy and uniform cutoff bounds

This continuation proves a local energy estimate for the actual operator

\[
P_c=-\Delta_y-c|y|^2\Delta_t,
\qquad (y,t)\in\mathbb R^4\times\mathbb R^{\kappa},
\]

where κ is any finite index type. Its evidence category is a fully compiled Lean theorem with explicit local PDE and local weak H² hypotheses. It does not prove that one weak Grushin equation by itself implies local H².

Let f and h be actual global complex L² classes. Let Ω be open and suppose f belongs to the existing actual cutoff-defined `ProductLocalWeakH2On f Ω`. Suppose P_c f=h in the compact-test distributional sense on Ω. For every real C∞ compactly supported η with support contained in Ω, the formalization constructs U=ηf and all genuine L² weak first and ordered second derivatives. Write a_v for its first derivatives and

\[
E_c(a)=\sum_{i=1}^4\int|a_{y_i}|^2
+c\sum_{j\in\kappa}\int |y|^2|a_{t_j}|^2.
\]

The exact identity is

\[
E_c(a)=\operatorname{Re}\int\overline{\eta^2 f}\,h
+\int\left(|\nabla_y\eta|^2+c|y|^2|\nabla_t\eta|^2\right)|f|^2.
\]

The local H² hypothesis is used to construct an outer compact plateau representative F=χf. Here χ=1 on an open neighborhood of the support of η. The original local weak PDE transfers to F on that neighborhood because differential operators do not enlarge a smooth test's support. The already verified compact weak H² energy identity applies to F. Every occurrence of F in the resulting identity lies under η or its derivatives, so it is exactly replaced by f. No bound on the outer cutoff enters the resulting energy identity. Genuine weak first-derivative uniqueness makes the identity valid for every actual first-jet representation of ηf, independently of the choices made in this construction.

The formal Caccioppoli consequence is

\[
E_c(a)\le\frac12\int\eta^2(|f|^2+|h|^2)
+\int\left(|\nabla_y\eta|^2+c|y|^2|\nabla_t\eta|^2\right)|f|^2.
\]

If η²≤D and the displayed derivative weight is at most C, the explicit bound is

\[
E_c(a)\le(D/2+C)\|f\|_2^2+(D/2)\|h\|_2^2.
\]

For each fixed c and cutoff η, a finite nonnegative constant depending only on these data is proved to exist such that E_c(a)≤Cη,c(‖f‖²+‖h‖²) for every permitted f,h,Ω. The automatic constant is selected noncomputably; no effective modulus or executable coefficient computation is claimed. The identities and these upper bounds hold algebraically for every real c. Their use as coercive energy estimates requires c≥0, with additional strict positivity where later spectator estimates divide by c.

The final bridge connects the local estimate to the quantitative commutator theorem. If η=1 on an open set V containing a measurable K, and a has the actual product formula a_v=ηd_v+(D_vη)F, then a_v=d_v almost everywhere on K. For c≥0,

\[
E_{c,K}(d)\le E_c(a).
\]

This proof establishes support of a in the compact support of η and proves global integrability of the weighted spectator terms before comparing restricted and whole-space integrals. It does not rely on Lean's totalized integral for a nonintegrable expression.

Source modules are `LocalWeakGrushinPlateau_v1`, `LocalWeakGrushinEnergy_v1`, `LocalWeakGrushinCaccioppoli_v1`, `LocalWeakGrushinUniformEnergy_v1`, and `LocalWeakGrushinPlateauJets_v1`. The exact declarations, source and object hashes, and expanded-statement/axiom receipts are recorded in `audits/LOCAL_WEAK_GRUSHIN_ENERGY_CHECKPOINT_v1.json`. All axiom dependencies are the declared standard foundations `propext`, `Classical.choice`, and `Quot.sound`. Development builds reused pinned Mathlib and project object caches. These modules postdate the completed v18 source-rebuild snapshot and are not represented as isolated-source-rebuilt here.

This extends the sealed compact-input energy checkpoint. Frozen historical sources remain unchanged: the original `RWA_REPORT.md` SHA-256 is `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, in freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.

The next composition is the quantitative cutoff-output bound for partially regularized actual weak solutions, followed by the existing bounded-derivative limit theorem. No analyticity, factorial recurrence, approximation rate, executable solver, new numerical interval, novelty claim, or full Theorem T is established by this checkpoint.
