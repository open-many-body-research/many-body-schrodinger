> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact quadratic principal commutator

This continuation establishes a pointwise Lean identity on the actual product
coordinates \(\mathbb R^4_y\times\mathbb R^3_t\). It identifies the quadratic
proper Leibniz sum in the differentiated Grushin equation with the precise raw
expression used by the separately sealed principal functional bound.

Let \(F_{\alpha,\beta}\) be any family of complex-valued raw functions, indexed
by \(\alpha\in\mathbb N^4\), \(\beta\in\mathbb N^3\). For a coordinate word
\(w\), define \(D_w=F_{a(w),b(w)}\), where \(a(w),b(w)\) count its Y and T
letters. Define its appended spectator trace by

\[
G_w=\sum_{j=1}^{3}D_{w\,t_jt_j}
   =\sum_{j=1}^{3}F_{a(w),b(w)+2e_j}.
\]

For \(q(y,t)=|y|^2\), let \(\mathcal C_q(G,w)\) be the sum over the actual
ordered Leibniz choices assigning at least one letter to \(q\), retaining
repeated choices. The final theorem proves, for every real \(c\), every point
\((y,t)\), and the canonical word \(w(\alpha,\beta)\),

\[
\begin{aligned}
c\,\mathcal C_q(G,w(\alpha,\beta))
={}&2c\sum_{i=1}^{4}\sum_{j=1}^{3}
 \alpha_i y_i F_{\alpha-e_i,\beta+2e_j}\\
&+c\sum_{i=1}^{4}\sum_{j=1}^{3}
 \alpha_i(\alpha_i-1)F_{\alpha-2e_i,\beta+2e_j}.
\end{aligned}
\]

Multiindex subtraction is coordinatewise natural subtraction. When a required
Y letter is absent, its prefactor is zero. No positivity of \(c\), weak
derivative existence, regularity, compatibility, integrability, or norm premise
is used: this is an identity for arbitrary \(F\).

The proof computes the actual directional Fréchet derivatives of \(q\).
Only a singleton Y letter contributes \(2y_i\); only two equal Y letters
contribute \(2\). Spectator derivatives, unequal Y pairs, and all coefficient
words of length at least three vanish. The ordered split list has exactly
\(\alpha_i\) selected singleton choices and \(\binom{\alpha_i}{2}\) selected
equal-pair choices. Count conservation identifies each remaining word with
the displayed natural multiindex. The factor \(2\) in the second derivative
then gives \(2\binom{\alpha_i}{2}=\alpha_i(\alpha_i-1)\).

The endpoint is
`TheoremT.Continuum.WeakGrushin.grushin_quadratic_principal_identification`
in `lean/GrushinQuadraticPrincipalIdentification_v1.lean`. Its right-hand side
is literally `factorialPrincipalRawError c F α β p`, not a separately defined
approximation to that expression.

The five new algebra modules contain 24 declarations, all compiled and audited
with strict auditor v7. Expanded statements have no omissions or printer
failures; axiom dependencies use only `propext`, `Classical.choice`, and
`Quot.sound` where needed. Existing pinned library objects were reused. These
new modules lie outside the prior isolated source rebuild v20 (817 targets).
No new dependency source rebuild was performed in this bounded task.

This result supplies the exact algebra needed to apply the prior principal
norm theorem to the genuine differentiated equation. It does not by itself
prove a norm bound, a factorial regularity rate, full Theorem T, or an
executable algorithm. The parent continuation owns those compositions.

Frozen provenance: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`, report
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
All historical and previously successful artifacts remain unchanged.
