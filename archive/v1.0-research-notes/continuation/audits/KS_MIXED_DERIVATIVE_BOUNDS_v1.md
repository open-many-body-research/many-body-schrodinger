> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit joint derivative bounds for the polynomial KS descent

This is a formal mathematical component of R04. It is not full Theorem T,
an executable energy solver, or a claim about the original sharp D6 constant.
The exact source and audit inventory is in
`HOMOGENEOUS_SPECTATOR_MIXED_DERIVATIVE_CHECKPOINT_v1.json`
(SHA-256 `584ae07faf6d3b8838fb908e4a4731065d3b4d37bfb2172a1a774613c2f91aec`).

Let (A_{m,\gamma}\) be actual complex polynomials in three variables,
homogeneous of degree (m\), indexed by (m\in\mathbb N\) and
(\gamma\in\mathbb N^d\). The coefficient norm is the literal finite sum
of the absolute values of the polynomial coefficients. Assume

\[
 \|A_{m,\gamma}\|_{\mathrm{coeff},1}\le C D^m S^{|\gamma|},
 \qquad C\ge0,\quad D,S>0.
\]

The previously verified original pair-index sum

\[
 F(X,s)=\sum_{(m,\gamma)\in\mathbb N\times\mathbb N^d}
 A_{m,\gamma}(X)s^\gamma
\]

converges normally on smaller product polydiscs and is jointly complex
analytic on (D\|X\|_\infty<1\), (S\|s\|_\infty<1\). Its norm on the
closed product polydisc of radii (r,h\) is at most
(C/[(1-Dr)(1-Sh)^d]\). These statements concern the actual ungrouped sum;
absolute summability is proved before the exact total-degree regrouping.

The new quantitative theorem gives, for every pair of finite multiindices
(\alpha\in\mathbb N^3\), (\beta\in\mathbb N^d\),

\[
 |\partial_X^\alpha\partial_s^\beta F(X,s)|
 \le 2^{d+1}C\,[4(3+d)D]^{|\alpha|}
                  [4(3+d)S]^{|\beta|}\alpha!\beta!
\]

on (D\|X\|_\infty\le1/4\), (S\|s\|_\infty\le1/4\).
The derivative is defined using the actual iterated complex Fréchet
derivative on a fixed finite coordinate word. The exact number of occurrences
of every coordinate is proved equal to its supplied exponent. Selection of
the word uses classical choice and is not advertised as executable.

The proof groups the terms by joint total degree. The exact number of
radial/spectator degree indices is (\binom{k+d}{d}\). For this derivative
estimate alone, the bound (\binom{k+d}{d}\le2^{k+d}\) produces a geometric
multilinear coefficient majorant. The proved derivative estimate for that
actual power series gives (2^{d+1}C4^k k!\) after inverse block normalization.
The local continuous-linear chain rule restores a factor (D\) or (S\)
for each direction separately. Finally the finite multinomial theorem gives
(k!\le(3+d)^k\alpha!\beta!\). This explains every factor in the displayed
bound. It does not reduce the previously established analytic domain.

For the prescribed real-input KS family (P_{m,\gamma}\), homogeneous of
degree (2m\), the input assumptions are its literal transformed-support
balance and the original-coordinate coefficient bound
(C b^{2m}S^{|\gamma|}\). The verified finite descent gives (D=32b^2\).
Its actual (A\) sum has the bound above, and its actual shifted (B\) sum
has the same bound multiplied by (D\). In the physical spectator dimension
(d=3\), the prefactor is (16C\), and the two rates are (24D\) and (24S\).
Actual physical Taylor and real-restriction consumers are separate modules
under active verification and are not assumed in this component statement.

All twelve declarations in the five primary modules compile in Lean
4.34.0-rc2 with pinned Mathlib
`d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. Complete expanded statements and
axiom reports were read and independently reviewed. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in these axiom reports. Pinned
dependency and continuation object caches were reused; this is not a new
isolated source dependency rebuild.

Historical reference preserved unchanged:
`rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`,
frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`.
