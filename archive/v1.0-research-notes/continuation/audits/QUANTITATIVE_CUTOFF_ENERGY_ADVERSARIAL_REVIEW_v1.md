> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused review of the quantitative cutoff and local energy chain

The completed statements reviewed contain no identified mathematical defect.
This review concerns the new cutoff bounds and local energy composition, not a
repeat audit of the continuum foundations. No PASS source was edited or
recompiled. The companion JSON records exact source/object fingerprints and
reparses six strict receipts covering 16 modules and 62 declarations. The newly
completed cutoff-output bridge is recorded separately in an append-only update.

The setting is the actual product Lebesgue space
`EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ`, with finite spectator index type
`κ`, complex actual L² functions, and real coordinate directional derivatives.
The principal expression is (P_c=-\Delta_y-c|y|^2\Delta_t), with zero potential.
`Jet` contains actual L² values; the derivative interpretation comes from the
explicit `WeakProductL2Directional` hypotheses. Those hypotheses are not hidden
inside a freely supplied operator or norm.

## Cutoff constants and integrability

Writing

\[
 S_c\chi=\Delta_y\chi+c|y|^2\Delta_t\chi,
 \quad W_c\chi=|\nabla_y\chi|^2+c|y|^2|\nabla_t\chi|^2,
\]

the actual commutator error is

\[
 E_\chi f=(S_c\chi)f+
 2\left(\nabla_y\chi\cdot d_y+c|y|^2\nabla_t\chi\cdot d_t\right).
\]

The negative sign occurs in (P_c(\chi f)=\chi P_cf-E_\chi f), consistently
with the formal `principal` definition. Weighted finite Cauchy uses weights

\[
 w_i=1\quad(i\in\mathrm{Fin}\,4),\qquad
 w_j=c|y|^2\quad(j\in\kappa).
\]

For (c\ge0), these weights may vanish and no division by them is used. The
proof therefore covers the degeneracy (y=0), and introduces no extra spectator
cardinality factor. The inequality for the squared norm of a sum gives exactly

\[
 |E_\chi f|^2\le2|S_c\chi|^2|f|^2+8(W_c\chi)\mathcal E_c(d).
\]

Here `firstJetEnergyOn c K d` is the sum of actual restricted integrals, including

\[
 c\sum_j\int_K |y|^2|d_{t_j}|^2.
\]

On compact (K), all such terms are proved integrable from actual L² jets and
continuous bounded weights. Both sides of every integral comparison have
integrability proofs. The commutator and its two component terms have actual
L² membership, and vanish off `tsupport χ`; hence restricting their integrals
to a compact set containing that support is justified.

For (|S_c\chi|\le A), (W_c\chi\le B), integration gives

\[
 \|E_\chi f\|_2^2\le2A^2\int_K|f|^2+8B E_{c,K}(d).
\]

The sharper norm bound is obtained by constructing both components in actual
L² and applying its triangle inequality:

\[
 \|E_\chi f\|_2\le A\sqrt{\int_K|f|^2}
       +2\sqrt B\sqrt{E_{c,K}(d)}.
\]

The square-root theorem explicitly requires (A,B\ge0). The squared theorem
needs only the pointwise coefficient inequalities; its proof derives the
required squared comparison where points of (K) occur. Empty (K) causes no
invalid sign inference: the corresponding restricted integrals are zero.

The existence of coefficient bounds follows from actual continuous cutoff
derivatives, compact support, and their vanishing off the support. Constants
are chosen for fixed (c,\chi,\kappa), before the input function and jets.
The explicit scalar bound is (A_Y+cR^2A_T), under the stated derivative and
support-radius bounds. These are existence theorems and explicit conditional
inequalities; they do not compute a modulus or an effective bound automatically.

## Local energy and a fixed family constant

The local energy identity constructs a smooth outer plateau, obtains genuine
whole-space weak H² jets for the corresponding cutoff, and then applies the
energy identity to the desired inner cutoff. Exact almost-everywhere identities
replace the outer-cutoff input by the original (f) wherever the inner cutoff
or its derivatives can be nonzero. Weak derivative uniqueness transfers the
identity to any actual first-jet representation of the same cutoff.

For (U=\eta f) and (a=DU), the identity is

\[
 E_c(a)=\operatorname{Re}\langle\eta^2 f,h\rangle
           +\int W_c\eta\,|f|^2.
\]

Young's inequality bounds the pairing by

\[
 \tfrac12\int\eta^2(|f|^2+|h|^2).
\]

For fixed bounds (eta^2\le D) and (W_c\eta\le W), this yields

\[
 E_c(a)\le(D/2+W)\|f\|_2^2+(D/2)\|h\|_2^2.
\]

The formal uniform theorem chooses (D,W\ge0) before quantifying over

`f h U Ω a`.

Thus (C=D/2+W) is independent of the solution, its source, and its selected
jets. No uniform family norm estimate is an implicit hypothesis. The energy
identity and its upper bound hold for arbitrary real (c) as signed statements;
their use as nonnegative energy estimates requires (c\ge0).

The plateau comparison proves derivative agreement on an open set on which the
cutoff is one. The use of an open plateau, rather than equality only on a closed
set, correctly makes its first derivatives vanish. Cutoff first jets vanish
almost everywhere off the compact cutoff support. That support is used to prove
global integrability of (|y|^2|a_t|^2) before applying the restricted-integral
inequality. The comparison requires (c\ge0); no subtraction or restriction of
a possibly nonintegrable weighted term is silently used.

The completed local energy statements still take globally L² (f,h), while
requiring only local weak H² regularity of (f). They do not themselves assert
the same theorem for arbitrary functions that are merely locally L². The local
L² extension and final uniform output composition have separate obligations.

## Output estimate and compact anisotropic bounds

The newly completed cutoff-output bridge derives the actual identity

\[
 H=\chi h-E_\chi f
\]

from the local compact-test PDE and genuine global weak H² jets. The original
weighted principal expression need not be globally L². The cutoff principal
output is constructed in L², and its global compact-test PDE is included in
the conclusion. Applying the norm-square inequality once more gives precisely

\[
 \|H\|_2^2\le2M^2\|h\|_2^2+4A^2\int_K|f|^2+16B E_{c,K}(d).
\]

The auxiliary theorem explicitly assumes the almost-everywhere formula; the
main bridge discharges it. Neither assumes the claimed norm estimate.

For compactly supported actual weak H² (f) satisfying the global PDE with
actual L² output (h), the anisotropic theorem with (c>0) concludes

\[
 \sum_i\|d_{y_i}\|_2^2\le2\|f\|_2^2+\tfrac34\|h\|_2^2,
 \quad\sum_j\|d_{t_j}\|_2^2\le\frac{\|h\|_2^2}{16c},
 \quad\sum_{i,j}\|e_{y_i y_j}\|_2^2\le\tfrac32\|h\|_2^2.
\]

The discarded weighted spectator and mixed terms are nonnegative for

(c\ge0).

Their actual integrability is supported by the compact weak H² approximation
chain: all second jets vanish off one compact set, continuous weights preserve
L² there, and weighted squared norms converge. The first bound uses the exact
directional integration-by-parts identity and four applications of

\[
 \|d_i\|_2^2\le\tfrac12(\|f\|_2^2+\|e_{ii}\|_2^2).
\]

The factor (2) is therefore specific to the four (y) coordinates. The
diagonal second-derivative sum is bounded by the full ordered (y)-Hessian sum;
combining with (3/2) gives (3/4). Division by (16c) correctly requires
strict (c>0). These constants are not uniform as (c\downarrow0).

This remains an a priori estimate for supplied genuine weak H² jets. It does not
itself construct derivatives for a rough weak Grushin solution, bound unweighted
second spectator derivatives, or establish the final limiting regularity gain.

## Evidence boundary

All six initial strict logs were rehashed and reparsed for exactly one full type
and one axiom record per declared result, with zero ellipses and only `propext`,
`Classical.choice`, and `Quot.sound`. Current source and object hashes match those
receipts. Expanded quantifiers confirm the fixed-cutoff placement of the uniform
constant, global actual L² types, genuine weak derivative hypotheses, and the
stated sign assumptions. The recorded environment reused pinned development
objects; this review is not a new source rebuild or compiler execution.

No claim of novelty, certified computation, or full Theorem T follows from this
review. The exact pending state is maintained by the companion JSON and its
append-only updates.
