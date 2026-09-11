> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Rational coefficient witnesses from actual H² column bounds, version 1

Evidence: an elementary paper lemma derived in this review. This is not an inherited theorem label, a Lean verification, or an implementation that can read unknown real coefficients. It supplements `OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_REVIEW_v1.md` at the root's request. No frozen file, successful module, prior review or receipt was changed. No compilation or isolated rebuild was performed.

Frozen provenance: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.

## 1. Exact abstract rounding statement

Let X be a real normed vector space (or a complex normed space with real coefficients), let m≥1, and let φ₁,…,φ_m∈X. Suppose b,h are nonnegative integers with

\[
\|\phi_i\|_X\le2^b\quad(1\le i\le m),\qquad
c\in\mathbb R^m,\quad\sum_i c_i^2\le2^h.
\]

For an integer p≥1, put

\[
\ell_m=\lceil\log_2m\rceil,\qquad t=p+b+\ell_m.
\tag{R1}
\]

For each i choose the nearest integer r_i to 2^t c_i, with a fixed tie rule, and put q_i=r_i/2^t. Then

\[
\left\|\sum_i(q_i-c_i)\phi_i\right\|_X
\le m2^{b-t-1}\le2^{-p-1}.
\tag{R2}
\]

The common denominator 2^t has at most t+1 binary bits. Set k=t+ceil(h/2). Since |c_i|≤2^(h/2), the real number 2^t c_i lies in [−2^k,2^k]. Its nearest integer also lies in this interval, because the endpoints are integers. Thus |r_i|≤2^k. Encoding a magnitude in ordinary binary and one sign bit uses at most

\[
 t+\lceil h/2\rceil+2
\tag{R3}
\]

bits per signed numerator. Reducing the fractions cannot increase these bounds. This explicitly distinguishes coefficient magnitude from the finite representation of rational coefficients.

Proof of (R2): |q_i−c_i|≤2^(−t−1), followed by the triangle inequality and m≤2^ell_m. No Gram eigenvalue or independence assumption is used in this rounding step. Such an assumption may have been needed to obtain the given h.

For completeness, ||q||₂≤2^(h/2)+sqrt(m)2^(−t−1)≤2^(h/2)+1/2, so ||q||₂²≤2^(h+2). We do not substitute this relaxed bound into an old algorithm without updating its constants. The original real-witness comparison in the fixed-shift algorithm does not need this substitution.

The real coefficient restriction is deliberate. Rounding complex coefficients componentwise to Gaussian dyadics introduces a factor sqrt(2); increasing t by one restores the same error target. The actual ground-state route under review uses real coefficients, so (R1) is the relevant version.

## 2. An explicit bound for the actual dyadic columns

Fix integer Z≥2 and electron count N=2. Let n≥1, \(z=1+\lceil\log_2(Z+1)\rceil\), and let the φ_i be the **original physical** dyadically scaled symmetric distance-polynomial exponentials, tensored with the normalized spin singlet. The spatial exponents are exactly Z2^j and degrees exactly ≤n−2j. No factor depending on an unknown state is added to a column.

Assume the domain and exact-moment facts declared in the frozen effective composition: φ_i∈H², reduced G_ii∈[1/2,2], and each of the three rational coefficients of the reduced Q_ii has numerator/denominator height at most

\[
\mathcal H=H_Z(n)=2^{40}(z+1)^2(n+2)^3.
\]

Use a height convention under which each represented rational has absolute value ≤2^mathcalH; increasing mathcalH by a fixed encoding bit covers an alternate endpoint convention. These are exactly the paper moment/height prerequisites, not new consequences of the approximation rate.

The actual physical moments are 8π² times the reduced moments. Using π<4, 0<log 2<1 and
\(Q_{ii}=q_0+q_1\log2+q_2\pi^2\), with |q_j|≤2^mathcalH, gives

\[
\|\phi_i\|_2^2=8\pi^2G_{ii}<2^8,\qquad
|Q_{ii}|\le18\,2^{\mathcal H}<2^{\mathcal H+5},
\]

\[
\|H_Z\phi_i\|_2^2=8\pi^2Q_{ii}<2^{\mathcal H+12}.
\]

Q_ii is nonnegative because it is the actual squared operator norm. Consequently

\[
\|\phi_i\|_2\le2^4,\qquad
\|H_Z\phi_i\|_2\le2^{\lceil\mathcal H/2\rceil+6}.
\tag{R4}
\]

An explicit graph-to-H² bound converts these to actual derivative control. Write F=||u||₂, G=||∇u||₂, X=||D²u||₂=||Δu||₂ and R=||H_Zu||₂. The Hessian is the full physical Frobenius Hessian. Hardy supplies a safe multiplier constant a=4Z+2 with ||Vu||₂≤aG. Plancherel and integration by parts give G²≤FX. Therefore

\[
\tfrac12X\le R+a\sqrt{FX}\le R+\tfrac14X+a^2F,
\qquad X\le4R+4a^2F,
\]

and

\[
F+G+X\le\tfrac32(F+X)
\le6R+(6a^2+\tfrac32)F
\le C_{\rm gr}(Z)(R+F),
\quad C_{\rm gr}(Z)=6(4Z+2)^2+2.
\tag{R5}
\]

This sum norm dominates the usual Hilbert H² norm and the physical H²_* convention used in the source. The frozen `dyadic_proof/EXTERIOR_CONSTANTS.md`, lines 95–115, supplies the same graph-bound argument with a sharper safe multiplier 3Z+2. Equation (R5) reproduces the calculation with the explicitly stated looser a. It assumes actual weak H²/domain facts, not smooth representatives at collisions. For a singlet column its scalar and full-spin norms agree.

For Z≥2, a≤5Z and C_gr(Z)≤151Z²≤2^(2z+6). Combining (R4)–(R5),

\[
\|\phi_i\|_{H^2_*}
\le2^{\lceil\mathcal H/2\rceil+2z+13}
\le2^{b_n},\qquad
\boxed{b_n=H_Z(n)+2z+20.}
\tag{R6}
\]

No gap, binding, actual eigenfunction, analytic chart, approximation order limit, or local regularity hypothesis is used in this column norm bound beyond the exact column domain and physical moment prerequisites.

## 3. The exact polynomial-height witness consequence

Assume a real dyadic coefficient vector c has the previously proved paper bound ||c||₂²≤2^(h_n), where

\[
h_n=2^{46}(z+1)^2(n+2)^{11},\qquad m_n\le(n+2)^4.
\]

Apply (R1) with b=b_n and h=h_n. The explicit grid exponent

\[
\boxed{t=p+H_Z(n)+2z+20+\lceil\log_2m_n\rceil}
\tag{R7}
\]

produces rational coefficients whose physical H² error relative to the real witness is at most 2^(−p−1), denominator height at most t+1 and signed numerator height at most t+ceil(h_n/2)+2. In particular the rational coefficient height is O_Z((n+2)^11+p), not exponential in n as a **bit length**.

If the starting physical trial is normalized, then its reduced squared norm is 1/(8π²)<1. The reduced Gram bound for c^TGc=1 extends by homogeneity to c^TGc≤1, so h_n applies to that actual normalized trial as well. Alternatively one can formulate the rounding lemma directly for any real c for which its norm bound is already known. This avoids mistaking a physical normalization for a rational operation on c.

Let u=Σc_iφ_i have physical norm one, let v=Σq_iφ_i, and let e=2^(−p−1). Then ||v−u||₂≤e and ||v||₂≥1−e≥1/2. If also ||(H_Z−E_Z)u||₂≤ε and the actual-domain residual estimate has constant C_op(Z),

\[
\left\|(H_Z-E_Z)\frac v{\|v\|_2}\right\|_2
\le\frac{\varepsilon+C_{\rm op}(Z)e}{1-e}
\le2(\varepsilon+C_{\rm op}(Z)e).
\tag{R8}
\]

The normalized coefficients q_i/||v||₂ are generally irrational. A finite rational certificate stores the q_i, exact dictionary data and the norm/moment quotient representation. It does not assert that the normalized vector has rational coefficients. Equation (R8) is a mathematical normalization argument, not a rational square-root instruction.

## 4. Constructivity and remaining implementation boundary

(R1) is a rational-existence proof for a specified real vector. It would be an effective rounding operation only with sufficient access to that vector; ties and interval uncertainty would need an executable rule if used algorithmically. The actual analytic witness is not supplied with such an oracle. Thus (R7) must not be relabeled as a polynomial algorithm for recovering its coefficients.

The frozen fixed-shift solver has a different route: it computes moments, rational matrix approximations and a rational negative witness via fraction-free elimination. Its common-denominator coefficient height is O_Z((n+2)^15), following matrix size O((n+2)^4) and input height O_Z((n+2)^11). Those operand-size estimates and common-denominator handling are stated in the paper composition and were checked in the prior computational audit. This review found no missing factor that invalidates their conservative stage exponent 140. The code-level integer operations, generator, directed rounding, solver and certificate-to-continuum connection still require an actual complete implementation and verification. A finite experiment or the existential rounding lemma supplies none of those missing proofs by itself.

The new content of this supplement is the explicit rounding schedule (R7), its actual H² column bound (R6), and the encoding/normalization distinction. It does not establish the physical approximation rate, close T02, or change the original dictionary or regularization schedule. An independent agent checked the real/complex distinction, error constants and column-bound calculation as review evidence only.

## 5. Fingerprints and coverage

- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_REVIEW_v1.md`
  SHA-256 `0d20d83eb6b8de92590b7492f3ffd7aa4bade2beb75f18a153b5c6a623c871eb`; coverage: full supporting review authored in this unit.
- `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_FINGERPRINTS_v1.json`
  SHA-256 `9ea13db4d4d6de39e81fe19ca3b561d8147e04e54291b2f8850fbb30a539d352`; coverage: source hash and selected ledger provenance.
- `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_COMPOSITION.md`
  SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`; coverage: full; exact moments, height bounds, reduced norm convention, rational witness size.
- `THEOREM_T_FREEZE_2026-09-09_212604/dyadic_proof/EXTERIOR_CONSTANTS.md`
  SHA-256 `db6e477f5ccdfdb06cf5edefa8059b2cbe13a9a69271017feca7c6ea0eca5409`; coverage: lines 1-40 and 83-129; graph coercivity proof used, not a new full exterior-decay audit.

Recorded UTC: 2026-09-10T18:56:28.426815+00:00
