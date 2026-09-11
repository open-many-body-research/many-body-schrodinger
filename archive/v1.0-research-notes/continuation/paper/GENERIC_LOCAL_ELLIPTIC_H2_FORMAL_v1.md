> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak H² from an actual L² Laplacian

Evidence category: fully formalized mathematical implication for every
finite-dimensional real inner-product space E with its actual Lebesgue measure.

Let Ω⊆E be open. Let f,w:E→ℂ be locally L² on Ω and suppose

    ∫ (Δφ) f = ∫ φ w

for every real C∞ compactly supported test φ with tsupport φ⊆Ω. Then for every
real C∞ compact cutoff χ with tsupport χ⊆Ω, there exists U∈L²(E;ℂ), equal to χf
almost everywhere, with genuine L² weak first and ordered second derivatives
in every direction.

More explicitly, the formal result supplies d:E→L²(E;ℂ) with

    ∫ φ d(v) = −∫ (Dᵥφ) U

for every direction v and every real smooth compact test φ. For each v,q there
is e∈L² satisfying ∫φe=−∫(D_qφ)d(v). Thus mixed derivatives are included. The
quantification over every compact cutoff is the explicit definition of local
weak H² used here.

Local L² is first encoded by L² on every compact K⊆Ω. A separate formal theorem
proves this is equivalent, on open Ω, to the usual neighborhood condition:
every x∈Ω has a neighborhood S with f∈L²(S). The proof uses compact induction,
measure restriction monotonicity, and the actual square-norm integral; the
definition is not an unproved regularity assumption.

The proof has two localization steps. The existing finite smooth bump-cover
theorem constructs an outer smooth compact η supported in Ω and equal to one
on a neighborhood of tsupport χ. From the first-gain checkpoint, F=ηf has
genuine weak first derivatives: the distribution formula

    ΔF = ηw − (Δη)f + Σᵢ Dᵢ(2(Dᵢη)f)

has a right side in H⁻¹, and the exact Bessel identity raises F from H⁰ to H¹.
Only local L² of f,w is used in this first step.

Apply the same distribution formula to the inner cutoff χ. Each divergence
coefficient 2(Dᵢχ)f equals 2(Dᵢχ)F almost everywhere, because the support of
Dᵢχ lies inside tsupport χ where η=1. The actual weak multiplier product rule
now gives an L² representative for each of its derivatives. Consequently
Δ(χf) has an actual global L² representative. The established global elliptic
gain then supplies all weak derivatives through order two.

The final module is GenericLocalEllipticH2_v1, with the neighborhood-input
corollary in GenericLocalL2Neighborhoods_v1. Its new composition dependencies are
GenericH1MultiplierDivergenceGain_v1 and GenericNestedCutoffH2_v1. The preceding
first-gain checkpoint contains the negative-Sobolev and local distribution
machinery. No derivative of f is assumed. No compact cutoff or smooth
approximation existence is assumed without its proved construction.

The same result is formalized on an ordinary Cartesian product Y×T of finite
Euclidean spaces, with its maximum norm and actual product Lebesgue measure.
Here the test operator is the sum of squared coordinate derivatives in any
orthonormal bases of the two factors. ProductLocalEllipticTransport_v1 pulls
the local L² restrictions and every compact test through the actual
measure-preserving linear homeomorphism from WithLp 2 (Y×T). The Euclidean
Laplacian is identified with that factor operator. ProductLocalEllipticH2_v1
then transfers the resulting cutoff and every first and ordered second weak
derivative back. The ordinary maximum-norm product is never identified with a
Euclidean norm by assumption.

The adjacent checkpoint records hashes and strict expanded-statement/axiom
audits for all six new modules and seventeen declarations. Only propext,
Classical.choice and Quot.sound occur. These are existence theorems, not an
executable differentiation procedure. The proof gives no quantitative local
H² estimate and makes no novelty claim.

Development builds reused the declared pinned dependency and continuation
objects. These modules are outside the 671-target desktop source-rebuild
snapshot. The continuum physical applications must still prove the displayed
local equation for their actual inputs. In particular, this theorem provides
the ordinary elliptic regularity needed to justify partial regularization in
the Grushin argument; it is not itself the weak Grushin estimate or a factorial
analyticity result. Full Theorem T remains unverified.

The frozen original RWA_REPORT.md is preserved, SHA-256
2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066,
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag
theorem-t-proof-freeze-2026-09-09. Earlier frontier records remain historical;
this new result discharges the ordinary local-H² obligation stated in the
first-gain checkpoint.
