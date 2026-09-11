> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the conditional endpoint-one-third construction

Date: 2026-09-09. Evidence: **independent paper review of a conditional theorem**, not Lean verification, a numerical certificate, or an unconditional statement about the atomic ground state. The reviewed final source is `ENDPOINT_ONE_THIRD_v3.md`, SHA-256 `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a`. Its unchanged dictionary and explicit physical hypotheses G1–G3 are part of the statement.

The frozen dependency checked for the tail substitution is `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/GLOBAL_DYADIC_ATTEMPT.md`, SHA-256 `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b`, particularly G5–G6 and G15–G27. Frozen commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`; tag: `theorem-t-proof-freeze-2026-09-09`. No frozen claim was edited or upgraded by this review.

No remaining defect was found in the finite-order cutoff, polynomial approximation, parameter balance, or their stated conditional composition. One standalone-lemma omission was identified during drafting: promising a real polynomial for an arbitrary complex holomorphic F is false (F≡i suffices). The final source explicitly assumes F real on K. The compatible germs are then real on their real chart neighborhoods by uniqueness from the real interior of K. This corrects the standalone lemma without changing the stated physical inputs, which already require real ψ.

## Finite-order extension and composition checks

For B=m+2, each probability box kernel has support radius 1/(2B). Their B-fold convolution has radius 1/2. Convolution with the indicator of [−3/2,3/2] therefore yields support [−2,2] and plateau [−1,1]. Assigning r≤m derivatives to distinct kernels gives a signed-measure convolution with total variation bound (2B)^r. At least two undifferentiated boxes remain, ensuring continuous derivative representatives. This proves the claimed C^m cutoff and vanishing support-boundary jets; no nonzero compactly supported analytic cutoff is asserted.

The new rational truncated-power formula also checks: B integrations of the interval indicator against box kernels give coefficient B^B/B!, shifts t+2−j/B and t−1−j/B, and alternating binomial coefficients. The auxiliary finite Bernstein checks are useful execution evidence but were not substituted for the all-order convolution argument.

At lattice spacing ℓ=h/16, supports of radius 2ℓ have at most 5³=125 overlap. A retained half-cell meets K, so its support remains within (5/2)ℓ<h/4 of its chart center, leaving at least h/2 for Cauchy estimates. The plateau cubes cover a real neighborhood of K, not merely K itself. Compatible germs therefore make every derivative through order two agree there, including at nonvertex cone boundaries.

At a point, inactive cutoff factors have zero derivative jets, so the ordered product weights involve at most 125 active cutoff factors plus one analytic factor. The 126-factor Leibniz sum yields the claimed derivative base 126·96=12096. The number of all charts is not raised to the derivative order. Positivity and telescoping of weights give the zero-order bound M, without an h^−3 factor.

For composition with 4cos, Faà di Bruno gives Stirling numbers with factor 4 per block. The injection selecting one representative of each set-partition block proves S(r,j)≤binom(r,j)r^(r−j). Thus the sum is bounded by (A+r)^r, with A=4·12096m/h, rather than by an extra r! times A^r. Since r≤m and h≤1, the chosen base 50000m/h is sufficient. This absence of an extra factorial is essential to the endpoint conclusion.

## Fourier-to-Chebyshev tail and the low-hq issue

In the high-hq regime, D=floor(q/3) and m=floor(hD/(4C₀)), C₀=50000, satisfy m≥8 and m≥hD/(8C₀). Integrating m times in a maximum-frequency coordinate produces coefficient bound 125M(C₀m/(hR))^m; tensor cosine grouping costs at most eight. There are at most 3(R+1)² triples with maximum frequency R, and two algebraic derivatives cost at most a constant times (R+1)^4. Therefore the C² tail is bounded by a constant times

\[
M4^{-m}D^m\sum_{R>D}R^{6-m}
\le\frac{CM D^7 4^{-m}}{m-7}.
\]

The condition m≥8 ensures convergence through two algebraic derivatives. Fourier uniqueness and uniform derivative convergence identify the resulting polynomial-series sum with the actual extension on the cube. Restriction to degree D in each coordinate has total degree at most q; it is not a total-degree-q cube of q³ degree per coordinate.

The small-hq branch is handled separately and correctly. Choosing Q=0 gives C² error at most 2Mh^−2 by Cauchy. With b=log(4)/(48C₀), hq<192C₀ implies exp(−bhq)≥1/256. Hence the stated error CMh^−2(q+1)^7exp(−bhq) holds after increasing C. Removing h^−2 in this branch would invalidate the proof. No unrestricted low-order C² Fourier-tail summation is used to avoid that cost.

For the same nonzero truncation, each coefficient is also bounded by 8M from its defining Fourier integral. There are at most (q+1)³ coefficients and two polynomial derivatives cost at most (q+1)^4 on the cube. This gives the explicit (q+1)^7 bound. Outside, standard real Chebyshev growth with total degree at most q gives the displayed conservative (6t)^q. The small-hq zero polynomial satisfies these growth bounds automatically. The outside bound concerns the actual polynomial used in the witness, not only its compactly supported extension.

## Global substitution and its exact scope

G1–G2 supply the common rescaled radius h_T=c_h(1+T)^−2 and bounded amplitude, exactly as the conditional G6 argument. The h_T^−2 penalty therefore costs (1+T)^4, while the new exponential is exp(−b′q/(1+T)^2). Taking M_(T,q)=C(q+1)^7(1+T)^4 dominates both the shell polynomial bounds and the finite-order global envelope required by the old lower and upper tail arguments.

Direct comparison with frozen G15–G23 confirms the substitution retains the same shell scale factor τ_j^(σ+1)(1+τ_j²), the same lower-tail vanishing powers, the actual polynomial exterior (6t)^q, and the same inner and physical outer omissions. Retaining the old extra (q+1)^4 factor is conservative. The geometric shell sum costs at most (1+T)^4, yielding the stated global prefactor (k+1)^3(q+1)^11(1+T)^8. The norm-conversion and Poisson estimates remain inherited paper dependencies with their original assumptions; this review does not formalize them.

At T=(q+1)^(1/3), both q/(1+T)^2 and the physical tail scale T are bounded below by positive multiples of q^(1/3). The other terms decay exponentially in q. The prefactor has power 3+11+8/3=50/3 and is absorbed into a weaker exp(−cq^(1/3)). The dictionary index is still exactly k+q+2(J+1)=769q+770 with k=J=256(q+1). Passing to arbitrary n by q=floor((n−770)/769) and treating finitely many smaller n separately is valid.

The residual transfer is separately conditional on the actual eigenvalue equation, H² domain, and |E|≤Z². Normalization is valid once the L² approximation error is at most 1/2. Neither this transfer nor the approximation theorem identifies the eigenvalue with the bottom of the actual continuum spectrum. The resulting coefficients depend on unknown analytic chart data; existence of these polynomials is not an implemented physical coefficient algorithm or a bit-complexity bound.

The defensible conclusion is therefore the conditional H² approximation rate Ce^(−cn^(1/3)) for the unchanged dictionary under G1–G3, with a separately stated conditional residual consequence. The endpoint is achieved by a degree-dependent finite-order construction, not by taking a singular limit of the earlier Gevrey theorem. Physical input verification, formalization, rational coefficient computation, certified energies, total termination and operational cost remain separate obligations.
