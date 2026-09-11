> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Finite balanced KS descent: coefficient growth

Let P be an actual complex polynomial in the independent spinor variables
z₁,z₂,w₁,w₂, homogeneous of total degree 2m. Suppose every exponent d in
its actual support is balanced: d₀+d₁=d₂+d₃. Then each row degree equals m.

The literal `ksBalancedPolynomialDescent P` pairs the monomial factors
using the previously verified natural-number pairing procedure and inserts
the four actual linear polynomials

\[
(r+X_2)/2,\quad (X_0+iX_1)/2,\quad
(X_0-iX_1)/2,\quad(r-X_2)/2.
\]

Each has coefficient L1 at most one. Powers, products and the actual
support sum therefore prove

\[
L_1(\operatorname{Descent}P)\le L_1(P).
\]

This norm inequality itself needs no balance hypothesis. Balance supplies
the separate physical evaluation identity and homogeneous output degree m.
Applying the proved radial reduction to this exact descended polynomial
gives outputs A,B with

\[
L_1(A)+L_1(B)\le L_1(P)\,2^m.
\]

The sharper prior bound uses \(3^{\lfloor m/2\rfloor}\); the base-two
bound is sufficient for the coarse analytic majorant. No factor two is
lost when adding the even and odd outputs, because their source monomials
form complementary parity classes.

If the coefficients of this balanced P obey the explicit majorant
\(|P_d|\le M B^{2m}\), with M,B nonnegative, the four-variable support
count gives \(L_1(P)\le M(4B)^{2m}\), and hence

\[
L_1(A)+L_1(B)\le M(32B^2)^m.
\]

These are exact Lean theorems about finite polynomials and the actual
definitions. The value 32 comes from \(4^{2m}2^m\), not from fitting a
claimed constant. Degree zero and the zero polynomial are included.

For integrating the real-to-spinor change of variables, preserve the
correct input: its coefficient-L1 nonexpansiveness transfers a bound on
the whole coefficient sum. It does not generally preserve an individual
coefficient majorant. Use `polynomialCoeffL1_balanced_radial_degree_bound`
with that transferred L1 bound. The more specialized geometric theorem
assumes its coefficient majorant on the balanced P itself.

This finite theorem leaves explicit the balanced-support condition and
the input coefficient bound. It does not show that actual physical Taylor
coefficients meet them, prove invariant series decomposition or passage
to a convergent descended analytic series, or supply executable complex
polynomial arithmetic and bit complexity. Those remain separate targets.

The final source and strict version8 expanded-statement/axiom audits use
Lean4.34.0-rc2 with the disclosed pinned Mathlib object cache. Only the
permitted foundational axioms occur; no new source rebuild is claimed.

Historical reference: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All work is in new continuation files.
