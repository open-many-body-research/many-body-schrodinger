> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# OPEN approximation: constructive and coefficient review, version 1

Evidence: focused adversarial paper review. No new Lean theorem, compilation, isolated rebuild, numerical experiment, or unconditional Theorem T result. This is supporting input to the root's requested `OPEN_APPROXIMATION_LEMMA_ADVERSARIAL_REVIEW_v1.md`, not a substitute for its combined analytic verdict.

The review finds **no actual-dictionary counterexample in the dyadic coefficient or finite-solver chain**. It does find elementary counterexamples to two weaker abstract inferences. The frozen dyadic argument states additional hypotheses that exclude those examples. The physical approximation rate remains a separate premise of this computational review; the present result is not a proof that the rate holds.

Frozen provenance: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. All old source, audit, receipt, and successful module bytes were preserved. Reviewed source fingerprints and exact reading coverage are listed below.

## 1. The two OPEN targets are separate

The priority-order sources have been reconciled. Their proximity in the checkout does not identify their theorems.

| Property | Stable correlated-Gaussian proposal | Exact dyadic atomic target |
|---|---|---|
| Inputs | Promised one- or two-nucleus, two-electron class; input length L; fixed geometric, charge, gap and ionization constants | Each fixed integer Z≥2, electron count N=2, approximation order n, requested energy precision p |
| Columns | Normalized primitives with rational positive-definite 2×2 exponent matrices and rational six-dimensional centers; standard spin followed by simultaneous antisymmetric projection | All symmetric ordinary distance monomials of degree ≤n−2j, multiplied by exp(−Z2^j S), j=0,…,floor(n/2), with unit spin singlet |
| Approximation | H¹ error ≤2^(−p); some real witness has coefficient norm squared ≤2^h | Actual physical H² existence error, hence actual continuum residual; original exponent 1/16, continuation's separate paper exponent 1/3 |
| Generation | Must supply explicit a,d and deterministic D(x,p), m,h≤a(L+p+1)^d, time≤a²(L+p+1)^(2d) | Exponents and degree allocation are already deterministic functions of Z,n; no search for centers or exponents |
| Coefficient protection | Stable witness bound is part of the OPEN hypothesis; redundancy and zero columns allowed | Rational positive-definite reduced Gram matrix and proved entry-height bounds supply an explicit bound for every normalized vector |
| Certification | Regularized form quotient; analytic H¹ approximation bound supplies the continuum lower endpoint | Regularized fixed-shift graph quotient; ground-branch separator and Temple give a posteriori enclosure |

The Gaussian lemma is equation (2) of `HELIUM_CERTIFICATION.md`, equation (6) of `helium_research/theorem_skeleton.md`. The latter equation numbering must not be confused with its primitive Gaussian formula (2). “Normalized” describes each primitive before antisymmetrization; the projected columns may have norm below one or be zero.

The later frozen dyadic composition explicitly retains only

\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
 e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\rm sym}(r,s,u),
\quad r=|x_1|,\ s=|x_2|,\ u=|x_1-x_2|.
\]

There is no proved reduction of the stable molecular Gaussian lemma to this fixed-charge atomic theorem, or conversely. T02 is the unverified dyadic Theorem T composition in the reviewed continuation, not the Gaussian generator conjecture. Neither the faster continuation rate nor a finite helium certificate silently discharges the Gaussian D/a/d/h obligation.

## 2. Precise obligation and dependence relevant to this review

Fix Z≥2 and the actual two-electron Coulomb Hamiltonian on the full fermionic spin space, with weak H² domain. Let E_Z be the actual spectral infimum and ψ_Z an actual normalized real ground eigenfunction with the rotation, exchange and singlet properties used by the distance dictionary. These physical facts require their own proofs; they are not consequences of a finite matrix definition.

For a stated exponent α>0, the H² approximation obligation is to prove constants C_A(Z),c_A(Z)>0, independent of n, and for every n≥1 one v_n in **exactly** V_n^(Z), such that

\[
 \|v_n-\psi_Z\|_{H^2_*}\le C_A(Z)e^{-c_A(Z)n^\alpha}.
\tag{Aα}
\]

Here H²_* counts actual physical L², gradient and full Frobenius Hessian norms, as in the source; equivalent norm conventions require an explicit constant change. The original α=1/16 and the continuation's α=1/3 are separately identified rate claims. No assertion uniform over unbounded Z, unknown states, or vanishing ionization margins is supplied.

The continuation's analytic rate constants depend on the named G1 vertex constants Cᵥ,Aᵥ,δᵥ,σ, the G2 exterior chart constants d,c_d,M_d, and the G3 physical tail constants C_t,γ, together with fixed Z and fixed geometry. The endpoint statement does not supply numerical formulas that turn those physical constants into an explicit Gaussian generator. This does not make them inputs to the adaptive dyadic energy algorithm.

The actual-domain estimate

\[
 \|(H_Z-E_Z)u\|_2\le C_{\rm op}(Z)\|u\|_{H^2_*}
\]

and eventual \(\|v_n\|_2\ge1/2\) turn (Aα) into a normalized residual rate. For example, the previously reviewed physical estimate uses the conservative constant \(C_{\rm op}(Z)=\sqrt6/2+4Z+2+Z^2\), with its declared physical norm convention and \(|E_Z|\le Z^2\). For sufficiently large n, one may take residual prefactor \(2C_{\rm op}(Z)C_A(Z)\); finitely many earlier n require an enlarged C_R(Z), using the already-present nonzero anchor. Thus the computational premise is precisely

\[
 \exists C_R(Z),c_R(Z)>0\quad\forall n\ge1:\quad
 \inf_{\phi\in V_n^{(Z)},\ \|\phi\|_2=1}
 \|(H_Z-E_Z)\phi\|_2\le C_R(Z)e^{-c_R(Z)n^\alpha}.
\tag{GRα}
\]

For the following height formulas use \(\nu_n=n+2\); the frozen composition writes an auxiliary “N=n+2”, which is not the electron count. Put

\[
z=1+\lceil\log_2(Z+1)\rceil,\qquad
H_Z(n)=2^{40}(z+1)^2\nu_n^3,\qquad
h_n=2^{46}(z+1)^2\nu_n^{11},\qquad m_n\le\nu_n^4.
\]

H_Z bounds rational entry numerators and denominators and their stated construction intermediates. The coefficient obligation actually proved at paper level is

\[
c^T G_n c=1\quad\Longrightarrow\quad\|c\|_{\ell^2}^2\le2^{h_n},
\tag{C}
\]

where G_n is the reduced rational Gram matrix in the exact dyadically scaled dictionary. The fixed angular factor 8π² is omitted uniformly from G,A,Q, as explicitly declared in the frozen composition. Physical normalization is performed analytically; all physical quotients agree. Changing the regularizer relative to this convention without its corresponding factor would be a different algorithm.

(C) is a magnitude bound on **real** witness coefficients, not a claim that those unknown coefficients have finite rational encodings. The finite solver outputs a different rational vector. Fraction-free witness recovery gives a common-denominator coordinate representation of height O_Z(ν_n^15). The distinction between existence, rational representation and executable recovery is essential.

The spectral constants used in the dyadic posterior enclosure are

\[
L_Z=-Z^2,\quad U_Z=-Z^2+5Z/8,\quad
\beta_Z=-5Z^2/8,\quad g_Z=\beta_Z-U_Z=Z(3Z-5)/8>0,
\quad\mu_Z=U_Z-E_Z>0.
\]

The rank-one complement lower bound at β_Z and strict μ_Z are separate ground-branch obligations. The coefficient bound (C) has no dependence on a spectral gap. The stopping constant depends on C_R,c_R,g_Z,μ_Z; the physical analytic constants can themselves depend on Z and decay margins. A Gaussian promised μ_gap is not interchangeable with β_Z or an ionization threshold.

## 3. Why the actual dyadic coefficient argument survives the attempted attack

The scaled reduced Gram entries are rational of denominator height B_n≤H_Z(n); the diagonal entries lie in [1/2,2]. Linear independence follows by fixing interior angular ratios, separating exponential polynomials in S, and then varying those ratios to separate the symmetric polynomial coefficients. No selected exponential is repeated in a different j block.

Let D be the product of the denominators of all m_n² entries. Every determinant monomial denominator divides D, so D det G_n is a positive integer. In particular

\[
\det G_n\ge2^{-m_n^2B_n},\qquad
\lambda_{\min}(G_n)\ge
2^{-m_n^2B_n}(2m_n)^{-(m_n-1)}.
\]

The second inequality uses positivity and trace G_n≤2m_n. No unsupported algebraic-independence assertion about log 2 and π² is involved: G is rational even though Q can lie in their rational linear span. Multiplying the denominator-product bound by an extra m_n is unnecessary; the single product already clears every determinant monomial. The displayed h_n dominates the negative logarithm of this lower bound and the other declared height bounds.

Thus every reduced-normalized approximation witness obeys (C), including a witness selected noncomputably in an analytic existence proof. This is a real quantitative lower Gram bound, although a very weak one. The phrase “no Gram assumption” means no extra conditioning promise is imposed on the physical inputs; it does not mean this concrete matrix inequality is absent from the dyadic proof.

The projected Gaussian Gram matrix is generally nonrational and can be singular. This determinant argument cannot simply be transferred to it. The Gaussian statement instead places the useful coefficient bound inside its OPEN approximation hypothesis.

## 4. The regularized finite solve does not need the analytic witness

The dyadic schedule is completely stated at paper level:

\[
\sigma=L_Z-1,\quad D_n=Q_n-2\sigma A_n+\sigma^2G_n,
\quad\tau_n=2^{-h_n-n-10},\quad\delta_n=2^{-n-10}.
\]

Since H_Z−σ≥I, T_n=D_n+τ_n I≥G_n+τ_n I. The normalized rate witness pays at most τ_n2^h_n=δ_n. Nonnegativity of the selected vector's regularizer then permits comparison of its unregularized physical shifted objective with that witness. This is the exact location where (C) is consumed; positivity of T alone would not suffice.

The remaining steps are an actual prescribed finite algorithm at the paper level: exact symbolic moments; signed rational interval evaluation; one common dyadic grid for matrix entries; exact rational positive-semidefiniteness tests and rational negative witnesses; bisection of the largest reciprocal quotient; exact rational mean; interval second moment; the filter m≤U_Z; outward dyadic rounding of the Temple interval; and a width comparison with 2^(−p). The lower threshold is tested initially, so the witness is defined even before a successful bisection update. Zero-diagonal indefinite blocks are handled explicitly. There is no exact-sign test of a transcendental matrix and no local numerical optimizer serving as a global guarantee.

The already-present constant-polynomial j=0 anchor gives a positive reciprocal lower bound 1/B₀ with B₀=(1+2Z)²+2. The prescribed entry error

\[
\zeta_n=\frac{\tau_n\delta_n}
 {2^{20}B_0^2m_n^2(2+2|\sigma|+\sigma^2)}
\]

controls reciprocal perturbations and subsequent second-moment contraction. After the rational witness is scaled to coefficient max norm one, its reduced norm squared is at least τ_n/(2B₀). Thus a polynomial number of guard bits suffices without assuming the returned vector is well conditioned in floating-point arithmetic.

The mere absence of an executable selector for the ψ-dependent shell polynomials does **not** invalidate this route. The finite solver finds a different vector in a deterministically generated full span. It does not require E_Z, C_R,c_R, ψ_Z, the analytic chart constants, or the shell coefficients as input. Conversely, the current source does not implement and formally verify the complete all-order loop. The existing fixed-tolerance experimental program is not that verified implementation, as both frozen and post-freeze audits explicitly state.

## 5. Bit-cost check and the exponents

The stated cost model charges binary operand sizes, exact division, common denominators and witness recovery. Its loose bounds are consistent on this review:

* m_n=O(ν_n^4), matrix precision s_n=O_Z(ν_n^11).
* One entry at precision s costs O_Z((ν_n+s)^12); m_n² entries cost O_Z(ν_n^140).
* Common-denominator fraction-free elimination has intermediate height O_Z(ν_n^15). The conservative total PSD/witness/contraction exponent is 53, below 140.
* An α residual rate gives a stopping order O_Z((p+1)^(1/α)), after the fixed μ_Z filter and outward-rounding allowances.
* Summing every stage, rather than charging only the final stage, gives exponent **141/α**.

Thus 2256=16·141 is consistent **conditional on α=1/16 and all stated physical and implementation premises**. If the independently reviewed unchanged-dictionary α=1/3 analytic theorem is correct, the same paper arithmetic would give a separately identified conditional exponent 423=3·141. This is not a newly composed unconditional theorem, an observed performance bound, or a machine-verified bit theorem. No actual α was established by this coefficient review.

The unknown positive RATE constants may appear in the mathematical fixed-Z runtime multiplier while being absent from the algorithm. This is legitimate for the frozen fixed-Z asymptotic statement; it does not furnish the Gaussian proposal's specified uniform a,d,D or prove efficiency as Z or electron count grows. The very large h_n makes literal early-stage execution impractical, which concerns performance rather than the distinction between polynomial bit length and exponential magnitude.

## 6. Explicit attempted breaks and their limits

### 6.1 Exact approximation does not imply stable coefficients

In R² let e₀,e₁ be orthonormal and take ε>0,

\[
\phi_1=e_0,\qquad
\phi_2=\frac{e_0+\varepsilon e_1}{\sqrt{1+\varepsilon^2}},\qquad
\psi=e_1.
\]

The columns are individually normalized, and ψ lies exactly in their span. Its unique coefficients are

\[
c_1=-1/\varepsilon,\quad c_2=\sqrt{1+\varepsilon^2}/\varepsilon,
\qquad \|c\|^2=(2+\varepsilon^2)/\varepsilon^2.
\]

This refutes a coefficient bound inferred solely from dimension, column normalization, or zero approximation error. Choosing ε=2^(−2^n) makes the logarithmic coefficient size grow faster than every polynomial in n, but it simultaneously introduces exponential representation height. It does **not** contradict the actual dyadic polynomial-entry-height premise. Nor does this abstract example constitute a physical correlated-Gaussian counterexample.

### 6.2 Positive regularization does not create a useful approximation witness

Use the same dictionary and H=diag(1,0), whose ground state is e₁. Choose shift σ=−1 and τ>0. For a unit physical vector v=a e₀+b e₁,

\[
 c_1=a-b/\varepsilon,\qquad
 c_2=b\sqrt{1+\varepsilon^2}/\varepsilon,
\qquad
 J_\tau(v)=4|a|^2+|b|^2+\tau\|c\|^2.
\]

If |b|²≥1/2, then J_τ(v)≥1+τ/(2ε²). The competitor e₀ has J_τ(e₀)=4+τ. Hence the strict inequality

\[
\varepsilon^2<\frac{\tau}{6+2\tau}
\]

excludes every global regularized minimizer with ground overlap squared at least one half. The finite continuous objective attains its minimum on the physical unit sphere. This is an actual counterexample to “regularizer positivity alone repairs conditioning.” The actual dyadic schedule avoids this inference by proving (C) and choosing τ_n from it. An independent agent checked the exact coefficients and threshold; that agreement is review evidence, not a formal proof.

### 6.3 H¹ approximation cannot be silently read as H² approximation

For nonzero smooth compactly supported χ on R⁶, let
\(w_k(x)=k^{-3/2}\chi(x)e^{ikx_1}\).
Then \(\|w_k\|_{H^1}=O(k^{-1/2})\to0\), while its first diagonal second derivative is
\(-k^{1/2}\chi e^{ikx_1}+O(k^{-1/2})\), so \(\|w_k\|_{H^2}\to\infty\).
One may choose χ supported away from all Coulomb collisions; the potential is bounded there and the Laplacian term also makes the operator residual diverge. Thus merely replacing H¹ by H² in the Gaussian lemma is invalid. This is a counterexample to a norm inference, not to the Gaussian form method, which deliberately needs only H¹, and not a lower bound for the exact dyadic approximation spaces.

### 6.4 The fixed finite-exponent obstruction does not refute this dictionary

Theorem C of the frozen two-electron report is an actual paper obstruction for a **fixed finite positive exponent set** with nonnegative distance powers. Its constants and inverse estimates depend on that fixed set. In the target dictionary the set expands and its largest exponent is Z2^(floor(n/2)). Treating that dependence as independent of n would be invalid. The fixed-set obstruction therefore cannot be quoted as a polynomial lower bound for the expanding spaces. No such lower bound was established in this scoped review.

## 7. What remains on the critical path

The coefficient and finite-algebra argument consumes exact domain conformity, exact physical moment formulas, rational Gram independence and height control, quantitative spectral separation, the residual-to-shifted-objective estimate, and the continuum enclosure theorem. It consumes GRα only for eventual success and the polynomial stopping order; correctness of an emitted posterior interval is conditional on the continuum spectral certificate premises, not on the rate. These facts must be connected to an actual implemented and verified all-order loop before T02 can close.

To obtain GRα by the continuation's chosen direct route, the analytic review must validate G1, G2 and G3 for the actual state, their compatible boundary/intersection charts, the one-vector global polynomial/window construction, physical H² error transfer and normalization. Local Lipschitz regularity and smoothness off collisions alone do not establish these all-order uniform analytic estimates. This supporting review does not re-audit their proof construction or upgrade the paper labels to Lean verification.

The direct endpoint theorem applies to f=ψ−ψ(0). It does not require an identified infinite Fock expansion or extraction of the particular κ_Z before constructing the final dictionary witness. The separate weighted RWA estimate holding for arbitrary finite κ cannot identify the physical Fock coefficient, but that limitation alone does not invalidate the direct ψ route. If the canonical review chooses an argument that actually uses sharper remainder extraction, that argument must restore the exact coefficient obligation explicitly.

Prior post-freeze reviews already exist: the 2026-09-09 approximation audit checked the conditional global window chain, the computation/spectral audit checked the effective composition conditional on GR, and the continuation root review checked the actual-eigenfunction paper composition. This is a focused renewed adversarial review, not the first post-freeze inspection. The old terminology error “moment field” was also corrected already: the used object is the rational linear span represented by triples. No new error is claimed from re-discovering that wording.

The four selected current ledger entries remain evidence-category records: A02_D01_new_rate, A03_tail_transfer and A03_exterior_decay are conditional paper results; T02 remains unverified. The fingerprint manifest captures the exact observed values so later changes to the active ledger do not alter what this review read.

Next action for root: combine this scoped result with the independent analytic adversarial findings, select the requested exact verdict for the actual OPEN statement, and continue only on its reduced dependency path. This review author has started no new regularity module, rebuild, or Rung 3–6 work after the priority change.

## 8. Source fingerprints and reading coverage

The paths below are relative to the actual workspace root. A hash of a source with partial reading coverage is not a claim to have reviewed its unlisted contents. Historical code-level verification is cited through the named prior audit, not re-executed or silently treated as new kernel evidence.

Observed UTC: 2026-09-10T18:51:59.635983+00:00

- `THEOREM_T_FREEZE_2026-09-09_212604/HELIUM_CERTIFICATION.md`
  SHA-256 `a29ba0101875bb621aba3ad954891502e4c8b3dd613ee1634197459fab052d44`; 34985 bytes. Coverage: full; priority source 1.
- `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/theorem_skeleton.md`
  SHA-256 `0d80f9e743d518b725ded4f705138716d62651313aa079ffdda708185eaddbf1`; 23943 bytes. Coverage: full; precise Gaussian generator and regularization quantifiers.
- `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`
  SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`; 49873 bytes. Coverage: full; omitted section 3 range recovered in a separate read.
- `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`
  SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`; 24955 bytes. Coverage: full; omitted section 2 range recovered in a separate read.
- `THEOREM_T_FREEZE_2026-09-09_212604/RATE_DICTIONARY_DECISION.md`
  SHA-256 `d9d15d0412ae5c8148aeeff6e264c8a2c0ae23df8dc8324929e698652146f303`; 38630 bytes. Coverage: dictionary/domain/moment statements and all Phase 4/final handoff; experimental middle not fully reviewed.
- `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_COMPOSITION.md`
  SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`; 18572 bytes. Coverage: full; exact effective bounds, finite solve and bit model.
- `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_AUDIT.md`
  SHA-256 `4c9e2674b8be8ca6d9bfe5a70ea019cb243ce620c175b9e5333b20fe973adea4`; 10231 bytes. Coverage: full; previous independent paper audit.
- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md`
  SHA-256 `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696`; 10182 bytes. Coverage: full; composed paper theorem and scope.
- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_APPROXIMATION_ROOT_REVIEW_v1.md`
  SHA-256 `b2d3f1625bfe31a07afd1bb01b99423c112b4a0443e4edbe9155c80a9ad2593a`; 2937 bytes. Coverage: full; historical independent composition review.
- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ENDPOINT_ONE_THIRD_v3.md`
  SHA-256 `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a`; 20526 bytes. Coverage: lines 1-120 only; exact G1-G3 and unchanged-dictionary statement, not a new full analytic proof audit.
- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/STATUS_LEDGER_v2.json`
  SHA-256 `5d797f382f828c7ae6fb2868d8913f9298e96b89efbec9fcf447284849a9c003`; 59824 bytes. Coverage: selected milestones T02, A02_D01_new_rate, A03_tail_transfer, A03_exterior_decay; mutable observed snapshot.
- `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/computation/COMPUTATION_SPECTRAL_AUDIT_v1.md`
  SHA-256 `7fdcc35e44c4fb2a9e3c0fa2ba529b68a13f8c8f1147c9530d5dc0e2c6b4a013`; 18608 bytes. Coverage: full; prior post-freeze exact computational audit, not re-executed.
- `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/approximation/APPROXIMATION_AUDIT_v1.md`
  SHA-256 `53ba43a396ac5bbe7a8a911d6c459df39c0deeab5cc0e31fd8a48b75540f7efe`; 22143 bytes. Coverage: full; prior post-freeze conditional approximation audit, not re-executed.
- `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/errata/MOMENT_SPAN_CLARIFICATION_v1.md`
  SHA-256 `e28aa172042612cb9225111a0366f311c26c3beca082926346d22353e58a3ef9`; 2272 bytes. Coverage: full; already-recorded terminology correction.
- `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/errata/ERRATUM_001_MOMENT_SPAN_v1.md`
  SHA-256 `007bd591382d81157a68e37ce76900216f95dd8979f6a7bc5db12992390b15b0`; 1500 bytes. Coverage: full; immutable historical issue record.

The companion `OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_FINGERPRINTS_v1.json` records these fingerprints, the priority attachment hash and the exact four observed ledger values.
