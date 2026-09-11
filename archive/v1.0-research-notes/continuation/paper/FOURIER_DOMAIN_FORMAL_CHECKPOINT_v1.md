> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual weak-H²/Fourier domain checkpoint, v1

The strongest result in this packet is fully formalized for the existing
configuration space, for every finite N and every actual scalar L² state f:

\[
\begin{aligned}
 \operatorname{HasH2}(f)
 &\iff \exists w\in L^2:
            \Delta(\iota f)=\iota w\\
 &\iff \operatorname{MemSobolev}(2,2,\iota f)\\
 &\iff [\,\xi\mapsto|\xi|^2\widehat f(\xi)\,]\in L^2 .
\end{aligned}
\]

The first predicate is the unchanged weak domain from
AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean, SHA-256
4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e:
it quantifies actual L² first derivatives and every ordered mixed second
derivative, tested against all real compact smooth functions. It is not a
new Fourier-defined substitute for the intended domain.

The exact final theorem names, in lean/ActualH2DomainEquivalence_v1.lean,
SHA-256 00daf8f078a08714716ec0082196d17705cfe90d4f8cfe723a6dc5d8912c11a6,
are:

- HasH2.exists_temperedDistribution_laplacian
- hasH2_iff_exists_temperedDistribution_laplacian
- hasH2_iff_memSobolev_two
- hasH2_iff_fourier_normSq_memLp

All names are in TheoremT.Continuum. In the first equivalence w is
existentially quantified. For a prescribed w, a statement that drops its
identification with the Laplacian would be false.

The final source and its expanded audit both compiled. Every audited theorem
in this packet depends only on propext, Classical.choice, and Quot.sound.
No sorry, sorryAx, added mathematical axiom, native_decide, or external proof
oracle is used to establish these results. Noncomputable mathematical
selection of derivative representatives occurs; no executable solver is
claimed by that selection.

## What was actually proved

The new proof bridges the original real compact-test WeakPartial predicate
to equality of derivatives on all Schwartz tests, in both directions.
The forward proof complexifies compact tests, multiplies a Schwartz test by
the actual scaled cutoff, and passes to the limit using the separately
compiled L² convergence of both cutoff tests and their actual first
derivatives. It uses continuous L² bilinear pairing. It does not invoke an
unproved Sobolev core or an assumed noncompact weak-test identity.

The Bessel identity
\[
 J_2T=T-(2\pi)^{-2}\Delta T
\]
has been compiled on genuine tempered distributions. If a distributional
Laplacian has an L² output w, the explicit L² element
\(f-(2\pi)^{-2}w\) witnesses order-2 Bessel regularity. Existing mathlib
Sobolev differentiation gives all first and mixed second L² distribution
derivatives, and the reverse test bridge converts them to the original
HasH2 witnesses.

In the other direction, the actual HasH2 first and ordered second weak
derivatives give the distributional Laplacian as the sum of the diagonal
second derivative witnesses. The coordinate orthonormal basis is the
existing EuclideanSpace basis, not an assumed coordinate Laplacian.

Two additional compiled multiplier lemmas close an integrability pitfall:
an actual L² product with a temperate multiplier has the expected
distribution embedding; conversely an L² output of the distribution
multiplier identifies the pointwise product almost everywhere and proves
its L² membership. They require no Lp membership of the multiplier itself.
The older mathlib theorem requiring that stronger premise cannot be
directly applied to global coordinate or norm-squared polynomials.

As a consequence, the packet also formally proves the actual a.e. L²
Fourier derivative and Laplacian formulas, and membership of their
polynomial products:
\[
 \widehat{D_v f}(\xi)=2\pi i\langle\xi,v\rangle\widehat f(\xi),
 \qquad
 \widehat{\Delta f}(\xi)=-(2\pi)^2|\xi|^2\widehat f(\xi).
\]
These formula theorems explicitly assume the corresponding genuine
distribution derivative output. The compiled WeakPartial equivalence
supplies that premise for the existing weak first derivatives.
The normalization is mathlib's exp(-2πi〈x,ξ〉); the pairing with tests is
bilinear, with no complex conjugation.

## Evidence and reproduction

The packet uses pinned Lean leanprover/lean4:v4.34.0-rc2 and mathlib revision
d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9. Builds used the pre-existing
compiled pinned dependency cache. No isolated full dependency-source
rebuild is claimed by this checkpoint. The program's separate isolated
rebuild records must be consulted before making a final reproducibility
claim, especially for newly used Fourier/Sobolev dependency branches.

From the workspace root, the existing runner invocation is:

~~~text
python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py ActualH2DomainEquivalence_v1
python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py ActualH2DomainEquivalenceAudit_v1
~~~

The runner records timestamped receipts. Reproduction in a new isolated
directory is preferable when preserving the completed compiled object too.
FOURIER_DOMAIN_BUILD_PROVENANCE_v1.json binds every current successful
source to a matching successful receipt and saved log.
FOURIER_DOMAIN_AUDIT_PROVENANCE_v1.json binds the fully expanded statement
audits, their saved logs, and parsed axiom lists.

The first default-budget expanded audits compiled but the printer elided
some subterms. They have been preserved. New
FourierBridgesExpandedAudit_v2 and ActualH2DomainEquivalenceAudit_v1 use a
1,000,000-step pretty-print budget; their complete saved output contains
zero printer ellipses. Raising the pretty-print or elaboration heartbeat
budget changes resource limits, not the trusted foundation.

## Scope and the next obligation

The accompanying paper
CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md, SHA-256
ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c,
gives exact configuration splitting, pair-rotation factors, spin summation,
weak density, and quantitative inequalities. Its formal-interface list is
a development snapshot; the domain bridges above are now discharged.
Independent bounded review found no mathematical error in that paper or
the actual-domain composition. The review specifically checked the
ordered mixed derivatives, Fourier normalization, polynomial-integrability
premises, and absence of circular domain assumptions.

The quantitative Hardy/Laplacian norm estimates in the paper remain separate
formal obligations unless their separate modules are cited. The current
packet does not itself prove Coulomb self-adjointness, its spectrum, the
variational/spectral ground-energy equality, binding, a ground-state vector,
Theorem T, or a certified energy algorithm. It is compatible with the
separate completed F02 Coulomb graph work; it must not be relabeled as all
of F03 or F04.

The next active application is the actual free resolvent with multiplier
\((2\pi^2|\xi|^2+\mu)^{-1}\), \(\mu>0\). The newly compiled weighted-Fourier
domain equivalence supplies its intended weak-H² domain. Range,
boundedness, perturbation, symmetry, and self-adjointness still require
their own proofs.

No frozen original artifact was changed. Historical project reference:
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, annotated tag
theorem-t-proof-freeze-2026-09-09.
