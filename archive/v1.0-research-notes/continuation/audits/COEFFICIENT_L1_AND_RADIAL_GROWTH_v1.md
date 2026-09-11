> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Literal coefficient norm and radial-reduction growth

For an actual `MvPolynomial σ ℂ`, define

\[
\mathcal L(P)=\sum_{d\in\operatorname{support}P}|P_d|.
\]

The sum is over the polynomial's actual finite support, even when σ is an
arbitrary type. The new Lean sources prove nonnegativity, definiteness,
the triangle inequality, exact complex scalar homogeneity, invariance
under negation, and submultiplicativity. In particular,

\[
\mathcal L(PQ)\le\mathcal L(P)\mathcal L(Q),\qquad
\mathcal L\Bigl(\sum_jP_j\Bigr)\le\sum_j\mathcal L(P_j).
\]

These properties are proved from actual coefficients; no unspecified
normed-ring structure is assumed. The addition proof extends coefficient
sums to the union of supports, preserving cancellation. Multiplication
uses the actual finite convolution expansion and two finite triangle
inequalities. A single monomial cXᵈ has norm |c| exactly.

For an actual polynomial substitution Gᵢ with \(\mathcal L(G_i)\le R_i\),

\[
\mathcal L(P(G))\le\sum_{d\in\operatorname{support}P}|P_d|
                    \prod_{i\in\operatorname{support}d}R_i^{d_i}.
\]

Hence generator norms at most one give a nonexpansive substitution. If
all generator norms are at most B≥1, then

\[
\mathcal L(P(G))\le\mathcal L(P)B^{\deg P}.
\]

The proof uses the literal `eval₂ C G` support formula, avoiding an
incorrect induction that would ignore possible cancellations in P.
The corresponding complex evaluation estimate is also proved, including
\(|P(z)|\le\mathcal L(P)\) on the closed unit polydisc.

For the actual radial reduction in `KSRadialPolynomialReduction_v1`, let
Q=X₁²+X₂²+X₃². Write dᵣ for the exponent of the fourth variable r. The
defined even and odd outputs A,B replace r^{2j} by Qʲ and r^{2j+1} by rQʲ.
The combined bound is

\[
\mathcal L(A)+\mathcal L(B)
\le\sum_{d\in\operatorname{support}P}|P_d|3^{\lfloor d_r/2\rfloor}
\le\mathcal L(P)3^{\lfloor\deg(P)/2\rfloor}.
\]

Each input monomial contributes to exactly one output, so no factor two
appears. This estimate holds for nonhomogeneous P as well. Under
\(\deg(P)\le m\), it gives the bound with \(3^{\lfloor m/2\rfloor}\),
and the elementary inequality \(3^{\lfloor m/2\rfloor}\le2^m\)
gives a convenient exponential majorant.

The finite reduction identity is the root agent's separately proved
\(P(X,r)=A(X)+rB(X)\) whenever r²=Q(X). The norm estimates establish
its quantitative coefficient cost. They do not assert homogeneity,
invariance of an arbitrary input, representation of an analytic KS
pullback by such input polynomials, or convergence of a descended series.
Those remain separate composition obligations.

All statements use the actual Mathlib multivariate polynomial operations
over complex coefficients. They do not supply executable rational
polynomial code or a bit-complexity theorem. The development builds and
strict version8 semantic audits use disclosed pinned dependency caches;
this checkpoint does not claim an isolated source rebuild or novelty.

Historical reference: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This is a new continuation manuscript.
