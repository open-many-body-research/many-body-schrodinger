> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# OPEN approximation lemma: Fock coefficient and vertex dependency review, version 1

Evidence: focused adversarial paper review, not a Lean theorem and not the canonical three-way verdict on the entire approximation/algorithm claim. The root conducts that verdict with the separate dictionary, stability and approximation reviews. No regularity module was started for this review. The preceding in-flight units were sealed under `QUANTITATIVE_H2_INFLIGHT_PREREQUISITES_DEFERRED_CHECKPOINT_v1.json` before this task.

The principal finding is that the direct wavefunction route does **not** require a convergent physical Fock expansion or identification of the leading logarithmic coefficient. It does require genuine **uniform factorial estimates** and quantitative coordinate descent. Those estimates are stronger than the now-formal finite-order regularity. A positive, normalized, symmetric, infinitely smooth countermodel below shows the logical difference. It is not a Coulomb solution and does not refute the actual physical approximation theorem.

## 1. Distinct targets and the exact analytic premise consumed

The frozen `HELIUM_CERTIFICATION.md` OPEN lemma asks for an oracle-free algorithm generating polynomially many rational normalized-primitive correlated Gaussians on a promised atomic/molecular class, an H¹ approximation, and coefficients with squared Euclidean norm at most 2^h. The dyadic endpoint paper instead uses

\[
 V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}
                  \mathcal P_{n-2j}^{\mathrm{sym}}(r,s,u)
\]

and proves a conditional H² existence rate. These are different dictionaries, input classes and norms. This subtask supplies no reduction between them. The source `RWA_REPORT.md` later composes the dyadic dictionary, not the Gaussian OPEN lemma. Its 2256 cost exponent is a separate computational chain. The ledger correctly keeps T02 unverified.

For the endpoint dyadic construction, the local input is G1 for **f=ψ̂−ψ(0)**: for some fixed C_v,A_v,δ_v>0 and 0<σ<1,

\[
 |\partial^\nu f|\le C_v A_v^{|\nu|}|\nu|!S^{\sigma-|\nu|},
 \qquad S=r+s,
\]

including ordinary derivatives of compatible analytic germs at every nonvertex closed-octant point. G2 is compatible holomorphic distance germs at S≥d, with radius c_d/(1+S) and amplitude M_d independent of the exterior center. G3 is exponential decay of the **physical** L², gradient and full Hessian norm, not just H¹ decay. No extracted remainder, logarithmic coefficient or Fock-series summability occurs in these definitions.

For actual eigenfunctions, local G1/G2 constants in the proposed paper route depend on Z, |E|, fixed chart geometry, and amplitude bounds such as the local Lipschitz constant and global L∞ norm. There is no local ground-gap premise. The gap or exterior coercivity instead enters the physical decay/certification chain and the effective stopping proof. Nothing here computes those constants or the unknown eigenfunction.

## 2. Which logarithmic coefficient is actually justified?

The locally archived primary Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen paper has kinetic term −Δ. Its Theorem1.1, equations1.8–1.12, gives a universal factor with

\[
 F_2=-\tfrac Z2(r_y+s_y)+\tfrac14u_y,\qquad
 F_3=\frac{2-\pi}{12\pi}Z(y_1\cdot y_2)\log(r_y^2+s_y^2),
\]

and a C^{1,1} residual. The coefficient was checked in the primary page image as well as extracted text. With y=2x, the physical kinetic convention −Δ_x/2 equals twice the source operator in y. Thus F₂ becomes f=−Z(r+s)+u/2, while

\[
 F_3(2x)=\kappa_Zq\log T+\kappa_Z(\log4)q,
 \quad q=x_1\cdot x_2,\quad T=r^2+s^2,\quad
 \kappa_Z=\frac{Z(2-\pi)}{3\pi}.
\]

The additional quadratic polynomial is absorbed into the C^{1,1} factor. This verifies the normalization of the finite leading-log factorization at paper/source level. It does not give an infinite physical Fock expansion. [Primary paper](https://arxiv.org/abs/math-ph/0312060).

When a₀=ψ(0)≠0, this specific κ_Z matters if the objective is the stronger extracted regularity. Indeed write ψ=e^{f+κ_Zq logT}Φ with Φ∈C^{1,1}, Φ(0)=a₀. Subtracting κa₀q logT from e^{-f}ψ leaves

\[
 \Phi+(\kappa_Z-\kappa)a_0q\log T+\text{a }C^{1,1}\text{ remainder}.
\]

The last assertion follows by twice differentiating qlogT(Φ−a₀) and the exponential remainder: their possible singular factors are multiplied by at least one additional radial power. Along a ray x=ρω avoiding pair collisions and with q(ω)≠0, the residual logarithmic term has radial second derivative

\[
 4(\kappa_Z-\kappa)a_0q(\omega)\log\rho+O(1).
\]

It cannot have bounded second derivatives when κ≠κ_Z. If a₀=0, this test does not distinguish κ; positivity at the vertex is a separate physical-ground-state fact.

By contrast, G1 with σ<1 does not distinguish κ. On a normalized shell, qlogT under positive scaling ε has size O(ε²(1+|logε|))=O(ε), and T has one common holomorphic logarithm branch bounded away from zero. Cauchy therefore gives the same weight-one estimate for every fixed finite κ. This is explicitly acknowledged in the new actual-eigenfunction paper. It would be invalid to infer the physical coefficient from that weak estimate; the direct ψ endpoint route bypasses the issue altogether.

Morgan's publisher abstract was rechecked. It distinguishes constructed Fock-type PDE solutions without the infinity condition from identification of the exponentially decaying physical eigenfunction. The full article remains subscription-only in this review; no unprinted theorem or derivative estimate is assumed. The original Fock text was not newly obtained. Neither is a dependency of the direct PDE route. [Publisher abstract](https://link.springer.com/article/10.1007/BF00526420).

## 3. Intersecting collision strata: exact two-electron geometry

For one fixed nucleus and N=2, the three physical collision sets are r=0, s=0 and u=0. Every intersection of two is x₁=x₂=0. Therefore on a normalized shell with r+s bounded below, the three pair sets are disjoint compact sets with positive separation. In half-perimetric coordinates, the nonzero axes are isolated pair collisions; the open faces are collinear configurations, not additional physical collisions.

This prevents a false obstruction: the paper proof does not apply an isolated-pair theorem directly at the triple vertex. It removes the vertex by scaling and proves uniform estimates as ε→0 on fixed normalized charts. The vertex need not be analytic; logarithms are allowed by the weighted bound. No conclusion about N≥3 intersections, simultaneous disjoint pairs, or molecular geometry follows from this special N=2 argument.

The primary 2009 theorem alone is insufficient for that uniform conclusion. Its Theorem1.4 explicitly restricts to isolated pair coalescences; it supplies neither a common scale-dependent constant nor the triple-point estimate. [Primary theorem](https://arxiv.org/abs/0806.1004). The proposed repair is the separate quantitative KS/PDE chain:

1. Actual weak pullback/removability across the KS fiber and correct c=4 or c=1 model equation.
2. A uniform O(1) L² amplitude for (ψ(εX)−a₀)/ε from physical Lipschitz regularity.
3. Common analytic bounds for the scaled coefficient and divided source, on fixed charts with separated spectator denominators.
4. Quantitative finite weak initialization, followed by the **separate all-order factorial recurrence**. Merely iterating qualitative smoothness supplies no factorial constant.
5. Quantitative KS coefficient descent, separate-coefficient rotational invariance, SO(2) invariant-series conversion, and boundary coordinate maps.
6. Compatible germs on full real neighborhoods, not just agreement on a normalized surface; fixed-scale differentiation and the comparison T_per≤S≤2T_per.

The new `GRUSHIN_FACTORIAL_RECURRENCE_v1.md` was read in full. It explicitly counts the weighted derivatives, derives the principal/cutoff commutators, decreases the integer cost, closes a finite geometric recurrence, and uses a fixed mixed-derivative embedding. No additional false inference was found in this focused reading. It remains a paper proof; the current finite weak gains do not silently turn it into a kernel theorem. The exact H12 initialization and quantitative descent are likewise separate obligations in a formal composition.

A known literal error in the frozen source path must remain visible: the source's degree-(n−1) second descent coefficient estimate with radial power n fails for the analytic KS lift u(y)=|y|², whose physical B coefficient is 1. `ISSUE_KS_SOURCE_DEGREE_v2.md` already records this and the separate direct-polynomial repair. The headline analytic-plus-distance theorem is not refuted. A continuation may use `KS_QUANTITATIVE_DESCENT_v1.md`; it may not revive the false bound as written in the frozen source.

## 4. Explicit countermodel to finite regularity ⇒ G1

The following model was proposed by the root and independently checked here. Let ρ=\sqrt{|x₁|²+|x₂|²} and set

\[
 H(\rho)=\exp[-\exp(\rho^{-2})]\quad(\rho>0),\qquad H(0)=0,
 \qquad
 \Psi(x_1,x_2)=C e^{-\rho^2}(1+H(\rho)),
\]

where C>0 normalizes the L² norm. It is strictly positive and invariant under rotations and electron exchange. Each fixed derivative of H is a finite sum of powers of ρ^{-1} and exp(ρ^{-2}) times exp[−exp(ρ^{-2})]; all vanish as ρ→0. Thus H(|x|) is flat C∞ at the origin. Away from it, H and Ψ are real analytic. Their distance reductions are analytic near every nonvertex closed-octant point because T=r²+s²>0 there. Gaussian damping gives global boundedness, global Lipschitz regularity, H² membership and exponential full-Hessian tails. Tensoring with the unit singlet gives the expected fermionic exchange symmetry.

Nevertheless G1 fails for every σ>0. On the perimetric edge a=b=0,c=t>0, S=2t, ρ=\sqrt2t, and the analytically continued difference is

\[
 F(z)=C\{e^{-2z^2}[1+\exp(-\exp(1/(2z^2)))]-1\}.
\]

G1 would bound its Taylor coefficients at every t by C_v A_v^k(2t)^{σ-k}. On a disk of radius proportional to t, avoiding zero, the geometric Taylor sum would therefore give |F(z)|≤2C_v(2t)^σ. Analytic uniqueness identifies that Taylor series with the displayed formula. But take the positive-near-real square-root branch

\[
 z_t=(t^{-2}+2\pi i)^{-1/2}.
\]

Then |z_t−t|=O(t³), so z_t belongs to every such proportional-radius disk for all sufficiently small t, while

\[
 \exp[-\exp(1/(2z_t^2))]=\exp[\exp(1/(2t^2))].
\]

The Gaussian prefactor tends to one and cannot cancel this positive double-exponential magnitude. This contradicts the proposed O(t^σ) bound.

This disproves an inference from even arbitrarily high finite Sobolev regularity, positivity, symmetry, punctured analyticity and exponential H² decay to G1. It does **not** satisfy the Coulomb PDE. It is not a physical eigenfunction counterexample, and it does not by itself prove failure of any approximation rate for Ψ. The frozen resolved-source audit already contains a related flat-function stress test; no novelty is claimed.

## 5. Reduced regularity inputs and boundaries

For the direct dyadic ψ route, retain only the analytic and tail results actually consumed:

- An actual normalized real, rotationally invariant and exchange-symmetric two-electron eigenfunction in the physical weak H² domain; the spectral justification is separate.
- Physical boundedness/Lipschitz amplitude estimates and the quantitative KS-to-distance chain giving G1 uniformly through normalized pair/collinear boundaries and approach to the vertex.
- The exterior analogue giving G2, with uniform chart coefficients and amplitude and the proved polynomial coordinate-radius loss. A uniform extraction estimate for e^{-f}ψ is not required when ψ itself is approximated. The exterior-specific review is separate.
- Exponential physical H² decay G3, or the proved transfer from an actual exponential L² tail and the actual eigenfunction equation. H¹ tails cannot be substituted.

Defer a full physical Fock expansion, higher Fock coefficients, C^{1,1} extraction beyond its independent historical role, arbitrary-N/molecular collision regularity, and unrelated observable or dynamics regularity unless a corrected target explicitly consumes them. A finite H12 bound is a sufficient initialization device in the current paper proof, not the approximation lemma itself. The new full quantitative H² composition remains deferred until the canonical review decides the required proof path.

This review supplies no new Gram or coefficient-height bound, Gaussian dictionary generator, finite solve, or bit-complexity theorem. The distinction is essential: detecting no local analytic counterexample is not a verdict that the combined OPEN approximation-and-stability lemma is proved.

## 6. Source and access record

Local copies were read before browsing. The 2005 coefficient was visually checked in its archived primary page3 image. The 2009 scope was checked from the archived primary text; current arXiv metadata/abstracts were corroborated at the links above. Morgan's current publisher abstract is accessible; full text remains subscription-only. No paid access, primary Fock text, or new Grušin source retrieval was undertaken. The new factorial proof was inspected directly and does not require accepting the compressed primary recurrence line without its replacement argument.

Frozen base: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. No frozen or prior successful artifact was edited. No isolated rebuild, numerical energy computation or further regularity formalization was performed for this review.

The following hashes identify the actual reviewed bytes; the scope column distinguishes full readings from targeted excerpts.

| Source relative to workspace | SHA-256 | Review scope |
|---|---|---|
| `THEOREM_T_FREEZE_2026-09-09_212604/HELIUM_CERTIFICATION.md` | `a29ba0101875bb621aba3ad954891502e4c8b3dd613ee1634197459fab052d44` | The single OPEN lemma and surrounding input/conditional-skeleton definitions; full displayed file read. |
| `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md` | `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79` | Sections 1–2 and section 5 leading-log factorization and radial obstruction; section headings and RATE boundaries checked. |
| `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | G1/G2/direct-state construction and final composition sections; all relevant assertions inspected. |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` | Full file, including normalized collision geometry, common factorial inputs, descent and extraction. |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` | Full file; compact estimates, weak initialization, finite threshold, all-order input and boundary audit. |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/EXTERIOR_ANALYTIC_ATTEMPT.md` | `6b56710d1a0ad8d4a2bcc20021b69412c1f073961f33243b3378ff50d0c731f5` | Full file displayed; exterior-specific details separately assigned to independent reviewer. |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/FOCK_SOURCE_AUDIT.md` | `22afddf6ece73481c32b98d03e8067ebe393cd28f09569f1e7de4b46f30e10ce` | Full file, source limitations, finite-log compatibility and countermodels. |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RESOLVED_SOURCE_AUDIT.md` | `f0f0b5e07fda02a7ccb817b7b40f8359fe571a67eb48eca1741825409214b85e` | Concrete derivative-weight mismatch and flat countermodel section, lines 126–154. |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2005_math-ph0312060.txt` | `cf3764fd6b2d96c449dd5330b85fa6eb00270f4c9b0d47db0b10207a465519bd` | Primary extracted text, Theorem1.1, equations1.8–1.12 and kinetic convention; lines70–225. |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2005_math-ph0312060_p3.png` | `8c70a40035e726e021c5b40dd05e85a4f8812391a4e293776657bfc6e1933c83` | Primary page3 image visually inspected, including C0=(2−pi)/(12pi). |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2009_0806.1004.txt` | `64ceb0f7a8708af5e87563c39d420a0500240f132d629c5c30f5677341fbf908` | Primary definitions1.5–1.10 and Theorem1.4; lines80–195. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md` | `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696` | Full file. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_APPROXIMATION_ROOT_REVIEW_v1.md` | `b2d3f1625bfe31a07afd1bb01b99423c112b4a0443e4edbe9155c80a9ad2593a` | Full file. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md` | `8e65d5d7053012e7b40d891f9a310794aa446f87dde902770a9c13ffe4635f3e` | Full file; explicit constants and closed-boundary cover. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ENDPOINT_ONE_THIRD_v3.md` | `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a` | Exact G1–G3 and dictionary, cutoff/extension and polynomial lemma definitions, lines1–165; global approximation proof not independently re-audited in this subtask. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/GRUSHIN_FACTORIAL_RECURRENCE_v1.md` | `5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594` | Full file; derivative costs, cutoff and principal commutators, finite recurrence and pointwise recovery. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/GRUSHIN_H12_WEAK_INITIALIZATION_v1.md` | `ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812` | Exact theorem and constants, lines1–105; full schedule identified, not re-audited here. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/KS_QUANTITATIVE_DESCENT_v1.md` | `17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f` | Exact theorem and constructive invariant-polynomial setup, lines1–145; full prior repair not reproved here. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ISSUE_KS_SOURCE_DEGREE_v2.md` | `44abbb70c9ca98714b2b960cdd19a83dad9e761cf428abc8f7c2bc1c1a3086c2` | Full file; known literal source estimate error and separately identified repair. |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/STATUS_LEDGER_v2.json` | `5d797f382f828c7ae6fb2868d8913f9298e96b89efbec9fcf447284849a9c003` | Entries A02_D01_new_rate, A03_tail_transfer, A03_exterior_decay,T02 extracted. This is a live ledger; recorded hash is this review snapshot. |
