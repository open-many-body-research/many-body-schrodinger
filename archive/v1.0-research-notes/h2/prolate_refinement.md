> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Separate prolate refinement investigation

**PROVEN (paper proof only)** for the analytic statements below. The prototypes perform exact rational interval calculations but are not Lean formalizations. The existing `gaussian_integrals.py` remains frozen at SHA256 `b8316ec0a3d19afa96d206bba3391e37e0fa5daed2a5a17723347189eeeca74b`; this investigation changes only this note and files under `h2/refinement`.

## Gaussian convention and the integral being enclosed

Let a>0 and let Y have the normalized Gaussian density (πa)^(-3/2) exp(−|Y−z e₃|²/a) on all of ℝ³. For two axial centers ±d e₃, with d>0, the existing prolate-coordinate calculation gives

    E[1/(|Y−d e₃| |Y+d e₃|)] = (1/a) ∫₋₁¹ f(t)dt,
    f(t)=exp[((d²−z²)/a)(1−t²)] erfc((d−zt)/sqrt(a)).

The d=0 limit is treated by the independently derived inverse-square identity below. The integration variable t is a coordinate substitution, not a Coulomb cutoff or a physical-space truncation. The prefactor and Gaussian convention match `moment_audit.md` and the existing engine. Every prototype input is an exact rational scalar. Its returned interval and actual width, rather than its requested tolerance, are authoritative.

## Different centers, with the Gaussian mean between them

Assume |z|≤d. Put K=(d²+z²)/a. Completing the square gives the entire function identity

    f(t)=exp[−(dt−z)²/a] erfcx((d−zt)/sqrt(a)),
    erfcx(w)=exp(w²)erfc(w)
            =(2/sqrt(π)) ∫₀∞ exp(−s²−2ws)ds.

The integral converges locally uniformly for complex w, since on any compact w-set its modulus is bounded by exp(−s²+Cs). It therefore defines an entire function, and agrees with exp(w²)erfc(w) on the real axis by completing the square; analytic continuation proves the identity everywhere.

Fix real t₀∈[−1,1] and complex h with |h|≤R. Write w₀=(d−zt₀)/sqrt(a)≥0. Then Re(w₀−zh/sqrt(a))≥−β, where β=|z|R/sqrt(a). Taking absolute values under the integral yields

    |erfcx(w₀−zh/sqrt(a))|
      ≤ (2/sqrt(π)) ∫₀∞ exp(−s²+2βs)ds
      = exp(β²) erfc(−β)
      ≤ 2 exp(β²).

Writing t=t₀+h=x+iy also gives

    |exp[−(dt−z)²/a]|
      =exp[−(dx−z)²/a+d²y²/a]
      ≤exp(d²R²/a).

Thus the uniform disk bound is |f(t₀+h)|≤2 exp(KR²). Cauchy's derivative estimate implies

    |f⁽¹⁶⁾(t₀)| ≤ 16! · 2 exp(KR²)/R¹⁶.

For K>0 choose the real radius R=sqrt(8/K). Its existence is enough: only R¹⁶=(8/K)⁸ enters the code. Since e<3,

    |f⁽¹⁶⁾(t₀)| /16! ≤ B,
    B=2·3⁸·(K/8)⁸.

This is a rational bound with no optimization oracle or floating radius selection. If K=0, d=z=0 and the exact expectation is 2/a.

For an interval of length L, eight-point Gauss–Legendre quadrature has error bounded by

    L¹⁷ (8!)⁴/[17(16!)³] · sup|f⁽¹⁶⁾|
      ≤ L¹⁷ (8!)⁴/[17(16!)²] · B.

This is the same Gauss remainder proved in `quadrature.md`. With k equal cells covering [−1,1], total expectation error is at most

    E_k = 2¹⁷ (8!)⁴ B/[17(16!)² a k¹⁶].

`refinement/prolate_cauchy.py` chooses the smallest integer k within its resource cap satisfying E_k≤tol/4, or retains the full error at the cap. It uses the existing certified Gauss nodes, positive weights and interval point evaluation of the original f, including extra precision for erfc subtraction. The complete interval quadrature error and E_k are retained. The result is intersected with [0,2/a], a valid bound by Cauchy–Schwarz and the single-center inverse-square expectation. The prototype rejects |z|>d: the preceding disk estimate must not be silently extended to that region.

## Same-center inverse-square expectation

For d=0, put T=z²/a≥0. The exact identity is

    E[1/|Y|²]=(2/a) F(T),
    F(T)=∫₀¹ exp[−T(1−t²)]dt.

In particular F(0)=1 and 0≤F(T)≤1. `refinement/square_series.py` uses two positive representations, with an explicit remainder in each case.

For 0<T<128, monotone convergence of the exponential series gives

    F(T)=exp(−T) Σₙ₌₀∞ b_n,
    b_n=Tⁿ/[n!(2n+1)].

The exact ratio b_(n+1)/b_n=T(2n+1)/[(n+1)(2n+3)] is at most T/(n+1). After including indices 0 through N, provided N+2>T, all ratios after the first omitted term are bounded by q=T/(N+2)<1. Therefore

    0≤F(T)−exp(−T) Σₙ₌₀ᴺ b_n
      ≤exp(−T) b_(N+1)/(1−T/(N+2)).

The implementation uses interval arithmetic and working precision bits+ceil(2T)+64; this choice improves usefulness but is not a substitute for the retained exact remainder and rounding width. If a term cap is reached before the ratio condition, it returns the independently valid [0,2/a] enclosure.

For T≥128, substitute u=1−t²:

    F(T)=(1/2)∫₀¹ exp(−Tu)(1−u)^(-1/2)du.

On 0≤u<1 the binomial series has coefficients c_n=binom(2n,n)/4ⁿ, with 0<c_n≤1 and recurrence c_(n+1)=c_n(2n+1)/(2n+2). Define, with N the highest included index,

    P_N(T)=(1/2) Σₙ₌₀ᴺ c_n I_n(T),
    I_n(T)=∫₀^(1/2) exp(−Tu)uⁿdu
          =n!/T^(n+1) [1−exp(−T/2) Σⱼ₌₀ⁿ (T/2)ʲ/j!].

The formula for I_n follows by repeated integration by parts, with I₀=(1−exp(−T/2))/T. On [0,1/2], the omitted binomial series is bounded by u^(N+1)/(1−u)≤2u^(N+1). Hence its contribution to F is at most

    ∫₀∞ exp(−Tu)u^(N+1)du=(N+1)!/T^(N+2).

The omitted interval [1/2,1] contributes at most

    (1/2)exp(−T/2)∫_(1/2)¹(1−u)^(-1/2)du
      =exp(−T/2)/sqrt(2)≤exp(−T/2).

Combining these positive remainders proves

    0≤F(T)−P_N(T)≤(N+1)!/T^(N+2)+exp(−T/2).

The prototype selects N using this complete rational/interval upper bound, stops at its resource cap or before the factorial bound begins increasing, and retains the actual error if the target is unmet. In particular, the fixed exp(−T/2) bound imposes a precision floor; this method does not promise arbitrary precision at a fixed split and finite N. Each incomplete-gamma bracket is clipped below at zero using its positive integral interpretation. The final interval is intersected with [0,2/a]. No quadrature or numerical differentiation enters the same-center branch.

## Scope of computational validation

Only the (2,2) same-center and (2,3) different-center kernels from the two dominant checkpoint pairs supplied by `h2_remote` are benchmarked. Their exact records are `h2/remote/cdfc567699c883eb56b747ef0c7d7138c037be55912e6efeb152879bce600b6d.json` and `h2/remote/e708e8b3a2eb49e6c036a54fa8e2876d2a60ea6dc5e7947ec54b633faa6e1f73.json`, from `trial_ecg_pruned_back64.json`. These examples identify a numerical bottleneck; they do not establish a whole-matrix certificate or complexity theorem. Exact prototype intervals, old/new overlap assertions and empirical CPU timings are written separately in `refinement/prolate_benchmark.json` and `.log`. No full matrix assembly or helium calculation is part of this investigation.

**EMPIRICAL:** bounded measurements at approximately 2×10⁻⁵ local tolerance were:

| Checkpoint prefix / potential pair | Old Taylor: seconds / cells / width | Prototype: seconds / work / width |
|---|---|---|
| cdfc5676 / (2,2) | 1.475 / 128 / 7.85×10⁻⁵, target unmet | 0.00120 / 3 terms / 9.49×10⁻⁷ |
| e708e8b3 / (2,2) | 1.523 / 128 / 6.39×10⁻⁵, target unmet | 0.00125 / 3 terms / 9.88×10⁻⁷ |
| cdfc5676 / (2,3) | 1.365 / 64 / 8.72×10⁻⁷ | 1.396 / 10 cells / 3.91×10⁻⁶ |
| e708e8b3 / (2,3) | 1.410 / 64 / 7.30×10⁻⁷ | 1.433 / 10 cells / 3.50×10⁻⁶ |

All four new enclosures meet the local tolerance and overlap the old certified enclosures. For same-center kernels, the series is over a thousand times faster in these two examples. For distinct-center kernels, the new method meets tolerance below the old sixteen-cell cap but is approximately equal in runtime to the successful old sixty-four-cell calculation: each Gauss cell has eight point evaluations. This distinction matters when choosing a selective refinement policy. None of these timings is load-bearing mathematical evidence.

An independent implementation audit passed seven inverse-square comparisons against an exact alternating series for the original integral, both square resource-cap branches, five prolate comparisons against the old Taylor enclosure, twenty derivative-bound comparisons, minimal-cell checks and input/domain rejection. The source and successful log are `refinement/independent_audit.py` and `.log`. The audited prototype hashes are `7d7e11588b7fa336bd03f424b4bb6bb59dcbf120703e836edf395e7e6ea406bb` for `prolate_cauchy.py` and `7e5011b3979613201e5feadb991556080a0761bf1f5877acbd6f09c1e73d7d85` for `square_series.py`. These checks add executable evidence; they do not change the paper-proof-only status of the analytic theorems.
