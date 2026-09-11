> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Conditional improvement of the Poisson-shell radius schedule

Date: 2026-09-09. Status: **conditional paper lemma; not Lean verified; not a ground-energy algorithm or a novelty claim.** This new file leaves every frozen artifact unchanged. Here electron count is fixed at **N=2**, approximation order is **n**, auxiliary shell degree is **q**, and **k=256(q+1)** denotes the Poisson order called `p` in the frozen proof. Requested energy precision is not a variable in this lemma.

Provenance: frozen `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md`, SHA-256 `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b`, within `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The relevant formulas are G1–G3, G6–G24, and G26–G27. Supporting frozen hashes are in `PROVENANCE_v1.json` beside this file.

## Precise conditional assertion

Fix Z≥2. Use the actual six-dimensional Cartesian variables x₁,x₂, distances r=|x₁|, s=|x₂|, u=|x₁−x₂|, and S=r+s. The target ψ is a real, rotation-invariant, exchange-symmetric function with ||ψ||₂=1. Its reduced representative in the closed half-perimetric octant has r=b+c, s=a+c, u=a+b. Write f=ψ̂−ψ₀, where ψ₀ is the continuous value at the physical origin.

Assume the following mathematical premises, as formulas about this actual ψ, rather than abstract data purporting to supply their proofs:

1. **Vertex premise G1.** For some fixed Cᵥ,Aᵥ,δᵥ>0 and 0<σ<1, every reduced multi-index ν satisfies |∂^ν f|≤Cᵥ Aᵥ^|ν| |ν|! S^(σ−|ν|) when 0<S<δᵥ, with compatible analytic germs across all nonvertex boundary strata.
2. **Exterior premise G2.** For one fixed d<δᵥ/8, every reduced point with S≥d has a compatible holomorphic extension to the complex polydisc of radius c_d/(1+S), uniformly bounded by M_d, for fixed positive c_d,M_d.
3. **Tail premise G3.** ψ∈H²(R⁶), and ||ψ||_{H²_*(S>R)}≤C_t exp(−γR) for R≥1, where C_t,γ>0. The norm H²_* counts the full Frobenius Hessian.
4. **Quantitative construction premise.** The shell-polynomial/Poisson-window construction satisfies the parameter-dependent estimate (B1) below, with C,b independent of q and T whenever the displayed admissibility conditions hold. This is the exact point at which the paper arguments G6–G24 are used. This lemma proves the schedule consequence of that estimate; it does not turn a preceding audit into a proof of G1, G2, G3, or the entire construction.

Then there are constants C₁,c₁>0, depending only on Z, the listed regularity/tail data and the construction constants, and vectors

\[
v_n\in V_n^{(Z)}=
\sum_{j=0}^{\lfloor n/2\rfloor} e^{-Z2^jS}\mathcal P_{n-2j}^{\mathrm{sym}}(r,s,u)
\]

such that

\[
\|\psi-v_n\|_{H^2_*(\mathbb R^6)}\le C_1e^{-c_1n^{1/10}}.
\]

If, additionally, ψ is an eigenfunction of the actual Coulomb operator H_Z=−(Δ₁+Δ₂)/2−Z/r−Z/s+1/u on its H² domain, with energy E_Z and |E_Z|≤Z², normalization gives unit vectors φ_n∈V_n^(Z) with

\[
\|(H_Z-E_Z)\phi_n\|_2\le C_2e^{-c_2n^{1/10}}.
\]

All coefficients in the construction may be real and unknown. Neither statement constructs a verified executable procedure for computing ψ, its coefficients, the constants, or certified ground-energy intervals.

## Admissible schedule and unchanged dictionary

For each integer q≥1, take

\[
k=J=256(q+1),\qquad T=(q+1)^{1/10},\qquad
a_j=Z2^j,\qquad \tau_j=k/a_j.
\]

Take q sufficiently large that

\[
k/T>Z,\quad 2^J\ge 2k/(ZT),\quad
2\tau_*<\delta_v,\quad \tau_*\le1,\quad T\ge16,
\qquad \tau_*:=k/(Z2^{J+1}).
\]

Such a finite threshold q_* exists. The first ratio is 256(q+1)^(9/10) and tends to infinity; exponential 2^J dominates every displayed polynomial; τ_* tends to zero; and T tends to infinity. All relevant thresholds can be enlarged to hold for every q≥q_*. This is a mathematical existence of a threshold, not an assertion that the unknown regularity data can be supplied to a program.

Let j₀ be the least nonnegative integer with a_{j₀}≥k/T. The first condition forces j₀≥1, while the second gives j₀≤J. Minimality gives

\[
T/2<\tau_{j_0}\le T,\qquad \tau_{j+1}=\tau_j/2.
\]

Use the same shell polynomials Q_{τ_j,q} of ordinary degree at most q as in G7–G8, rescaled as P_j=τ_j^σ Q_{τ_j,q}(·/τ_j), and the same finite windows

\[
E_k(t)=e^{-t}\sum_{\ell=0}^{k}t^\ell/\ell!,\quad
W_{j,k}(S)=E_k(a_jS)-E_k(a_{j+1}S).
\]

The vector remains exactly

\[
v_q=\psi_0E_k(a_{j_0}S)+\sum_{j=j_0}^{J}W_{j,k}(S)P_j.
\]

Its largest node index is J+1 and its ordinary polynomial degree at every node is at most k+q. Therefore

\[
v_q\in V_{k+q+2(J+1)}^{(Z)}=V_{769q+770}^{(Z)}.
\]

No cutoff, new exponent, negative power, logarithmic basis vector, or physical-domain replacement enters this formula. Finite distance-polynomial exponentials belong to the actual H² domain: their possible distance Hessians are proportional to 1/r,1/s,1/u, square-integrable in the corresponding three transverse variables, and their tails decay exponentially.

## The parameter-dependent bound being used

The construction premise is

\[
\begin{aligned}
\|\psi-v_q\|_{H^2_*}
\le C(k+1)^3(q+1)^4(1+T)^{66}\bigg[
&e^{-b\sqrt q/(1+T)^4}+e^{-k/16}\\
&+e^{-\gamma T/16}
+\left(\frac{k}{Z2^{J+1}}\right)^{\sigma+1}\bigg].
\tag{B1}
\end{aligned}
\]

This is G24 with the Poisson order renamed. Although the frozen G10 fixes T=(q+1)^(1/16), its preceding approximation lemma G6–G9 is quantified for all T≥1 and τ≤T. Its subsequent arguments G15–G23 use only these scale bounds and the displayed eventual conditions, not the identity T=(q+1)^(1/16). Specifically: the geometric sum in G18 is bounded by C(1+T)^4 for every such T; the polynomial-tail integral G16 depends on k,q and not on that identity; the inner cutoff conditions are precisely the τ_* conditions above; and T≥16 makes all tail radii lie in the original G3 range. Thus repeating those inequalities establishes (B1) for the new schedule **provided their analytic premises and estimates are valid**. This conditional scope is essential.

## Exact balance and polynomial absorption

For q≥1, k+1≤257(q+1), 1+T≤2(q+1)^(1/10), and q+1≤2q. Therefore the prefactor in (B1), without C, satisfies

\[
(k+1)^3(q+1)^4(1+T)^{66}
\le257^3 2^{66}(q+1)^{68/5}.
\tag{B2}
\]

The shell exponent satisfies

\[
\frac{b\sqrt q}{(1+T)^4}
\ge \frac{b}{16\,2^{2/5}}q^{1/10}.
\tag{B3}
\]

The second and third exponentials are bounded respectively by exp(−16q^(1/10)) and exp(−γq^(1/10)/16).

For the inner term, the elementary integer inequality k≤2^(k/2) holds for k≥4: it is an equality at k=4, and the induction step follows from (k+1)/k≤5/4<√2. Consequently

\[
\left(\frac{k}{Z2^{k+1}}\right)^{\sigma+1}
\le \exp\left[-\frac{(\sigma+1)\log2}{2}k\right]
\le e^{-128(\sigma+1)(\log2)q^{1/10}},
\tag{B4}
\]

where discarding Z^(−σ−1)2^(−σ−1) only enlarges the bound because Z≥2.

Put

\[
\eta=\min\left\{\frac{b}{16\,2^{2/5}},16,
\frac\gamma{16},128(\sigma+1)\log2\right\}>0.
\]

Equations (B1)–(B4) give

\[
\|\psi-v_q\|_{H^2_*}
\le4C257^3 2^{66+68/5}q^{68/5}e^{-\eta q^{1/10}}.
\]

For x=q^(1/10), q^(68/5)=x^136. The function x^136 exp(−ηx/2) has finite maximum (272/(eη))^136 over x≥0. Hence, for example,

\[
\|\psi-v_q\|_{H^2_*}\le C_*e^{-\eta q^{1/10}/2},\qquad
C_*=4C257^3 2^{66+68/5}
\max\{1,(272/\eta)^{136}\}.
\tag{B5}
\]

This displays why the polynomial factor does not destroy the improved stretched exponential.

## All approximation orders and continuum residual

For sufficiently large n put q=⌊(n−770)/769⌋. Then 769q+770≤n. For n≥3078, q≥n/1538, and for n≥769q_*+770 the q threshold is met. Monotonicity V_m^(Z)⊆V_n^(Z) for m≤n gives the claimed n^(1/10) estimate, with c₁=η/(2·1538^(1/10)). For finitely many smaller n take v_n=0 and enlarge C₁; ψ∈H² makes their errors finite.

For the residual conclusion, sliced Hardy and the Laplacian trace inequality give the genuine continuum bound

\[
\|(H_Z-E_Z)e\|_2\le
\left(\sqrt6/2+4Z+2+Z^2\right)\|e\|_{H^2_*}.
\]

For sufficiently large n, ||ψ−v_n||₂≤1/2, so ||v_n||₂≥1/2 and φ_n=v_n/||v_n||₂ is admissible. Since (H_Z−E_Z)ψ=0,

\[
\|(H_Z-E_Z)\phi_n\|_2
\le2\left(\sqrt6/2+4Z+2+Z^2\right)C_1e^{-c_1n^{1/10}}.
\]

For the finitely many remaining indices use the normalized anchor e^(−ZS), which belongs to V₀^(Z) and H², and enlarge the constant. Tensoring these exchange-symmetric spatial functions with the normalized spin singlet preserves every norm and makes them fermionically antisymmetric for N=2.

## Meaning and limits

Among substitutions T=(q+1)^θ into (B1), with 0<θ<1/8 and all other allocations fixed, the certified exponential power is min{θ,1/2−4θ}. This is maximized at θ=1/10. This optimizes only this particular upper-bound balance; it is not an optimality theorem about the dictionary or the physical wavefunction.

The change from the frozen power 1/16 to 1/10 is a new explicit conditional deduction, not a repair of a false frozen rate. The regularity premises, their uniform constants, and all algorithmic, rational-arithmetic, spectral-identification and bit-cost obligations retain their independent verification status. No novelty is inferred from the absence of a matching literature search result.
