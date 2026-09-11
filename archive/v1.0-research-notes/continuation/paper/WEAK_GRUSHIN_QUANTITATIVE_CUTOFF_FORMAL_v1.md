> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Quantitative weak Grushin cutoff estimates and uniform local output

Evidence category: fully compiled and axiom-audited mathematical implications
for the stated genuine weak differential equations. This is a continuum
functional-analytic result, not an executable procedure or a proof of full
Theorem T.

## Exact setting

Let X=R^4×R^m with its actual product Lebesgue measure, complex-valued L²
functions, and P_c=-Δ_y-c|y|²Δ_t, c≥0. In Lean the spectator coordinates are any
finite type κ. Every weak directional derivative is defined by equality against
all real smooth compactly supported tests on the ordinary product. Ordered
second derivatives have the same genuine weak definition. The product
representation uses the ordinary product topology and measure; the earlier
WithLp 2 bridges justify Euclidean transport where needed.

Write d for the actual first weak jet of F. For a real smooth compact cutoff χ,
put

A_χ=Δ_yχ+c|y|²Δ_tχ,
B_χ=|∇_yχ|²+c|y|²|∇_tχ|²,
e_c(d)=Σ_i|d_yi|²+c|y|²Σ_j|d_tj|²,
E_K(d)=∫_K e_c(d).

All these are the derivative expressions in the formal definitions. For every
compact K containing supp χ, E_K(d) is finite from the actual L² jets. No global
integrability of |y|d_t is assumed.

## Quantitative commutator

The prior actual weak product rule gives

P_c(χF)=χP_cF-C_χ(F,d),
C_χ(F,d)=A_χF+2(∇_yχ·d_y+c|y|²∇_tχ·d_t).

The new proof establishes weighted finite Cauchy, valid even when weights
vanish, and therefore

|C_χ(F,d)|² ≤ 2|A_χ|²|F|²+8B_χ e_c(d).

If |A_χ|≤A and B_χ≤B on K, integration gives

||C_χ(F,d)||²_2 ≤ 2A²∫_K|F|²+8B E_K(d).

For A,B≥0 a separate proof of the scalar and first-jet component estimates,
followed by the actual L² triangle inequality, gives the stronger bound

||C_χ(F,d)||_2 ≤ A sqrt(∫_K|F|²)+2 sqrt(B) sqrt(E_K(d)).

The finite Cauchy step inserts no extra factor of m. This is not a claim that
all cutoff constants, approximation rates, or complexity bounds are uniform in
m. No sharpness or optimality claim is made.

Each smooth compact cutoff has finite global A,B, proved from compactness and
vanishing off the cutoff support. An explicit scalar estimate is also proved:
if |Δ_yχ|≤A_Y, |Δ_tχ|≤A_T, A_Y,A_T≥0, and |y|≤R on supp χ, then
|A_χ|≤A_Y+cR²A_T. The root coefficient modules prove the corresponding explicit
gradient estimate B_χ≤a²+cR²b² when the separate gradient square sums are bounded
by a² and b². Automatic selection of a bound is a noncomputable existence
result; it is not an implementation for calculating constants.

## Actual local output and uniform bound

Suppose F has genuine global weak H² jets and P_cF=h on an open V containing
supp χ, in the compact-test sense. For |χ|≤M the construction supplies actual
L² U,H, all true first and ordered second jets of U, U=χF almost everywhere,
U zero off supp χ almost everywhere, H equal to the principal second-jet
expression, and P_cU=H against every compact smooth test. The local equation
itself proves H=χh-C_χ(F,d); this formula is not a theorem hypothesis. The bound is

||H||²_2 ≤ 2M²||h||²_2+4A²∫_K|F|²+16B E_K(d).

The final theorem needs only f,h∈L²(X), local genuine weak H² regularity of f on
open Ω, and P_cf=h on Ω. For any real smooth compact χ supported in Ω, it proves

∃C≥0, ∀such f,h, ∃U,H and genuine first/second jets:
U=χf a.e., supp U⊆supp χ a.e., P_cU=H,
||U||²_2≤C||f||²_2,
||H||²_2≤C(||f||²_2+||h||²_2).

The constant is chosen before f and h. A middle smooth cutoff η is constructed
with η=1 on a neighborhood of supp χ and supp η⊂Ω. An outer plateau produces
global genuine H² F equal to f near supp η. The actual first jets a of ηF equal
the jets d of F near supp χ. Their compact support supplies weighted
integrability before the comparison E_suppχ(d)≤firstEnergy(a). The already
formal local Caccioppoli estimate for ηf bounds this energy by
E(||f||²+||h||²), with E fixed by η and c. Also ∫_suppχ|F|²≤||f||². Thus the
formal proof may take C=3M²+4A²+16BE. No uncontrolled outer-cutoff derivative
norm enters the conclusion, and the proof does not assume a uniform bound on
the principal output.

## Verification and remaining boundary

Fourteen new modules contain 42 audited declarations. Exact source/object
hashes and five strict expanded-statement/axiom receipts are recorded in
`audits/WEAK_GRUSHIN_QUANTITATIVE_CUTOFF_CHECKPOINT_v1.json`. All final statements
compile with only propext, Classical.choice and Quot.sound among their axiom
dependencies. The sources were read directly; weighted integrability,
restriction to K, the local principal identification, and the order of the
uniform quantifiers were checked. The formal build uses Lean 4.34.0-rc2 and
pinned cached Mathlib and continuation dependencies. These modules are newer
than the completed 671-target desktop isolated source rebuild and have not yet
been included in a fresh isolated source rebuild.

The final theorem still assumes actual local weak H² of its input. Removing
that assumption for arbitrary L² weak Grushin solutions requires the separately
active regularization and limit argument. This checkpoint proves neither
analyticity nor factorial estimates, the original approximation rate, spectral
certification, an executable solver, complexity, or full Theorem T. It makes no
novelty claim.

The preserved original claim source is `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen at
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. No frozen original or earlier successful
proof was changed.
