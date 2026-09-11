> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent audit of the bounded-overlap conditional approximation improvement

Date: 2026-09-09. Evidence category: conditional paper argument, independently checked. This document supplies no Lean verification, executable coefficient generator, numerical certificate, or unconditional theorem about the physical ground state.

## Scope and outcome

This is a focused check of replacing the cutoff accounting in frozen G9, then substituting into G15–G24. It is not a new broad audit of the inherited analytic inputs or the global Poisson construction. The argument below supports the replacement, provided the chart support geometry is fixed as specified. No substantive error was found in the proposed exponent

\[
\frac{1}{s+2}=\frac{a}{3a+1},\qquad s=1+1/a,\quad a\in\mathbb N,\ a\ge1.
\]

Every constant may depend on the fixed integer a. No uniform control as a tends to infinity is established. In particular this proves no endpoint exponent 1/3.

## 1. A cutoff with the needed Gevrey order

Define u_a(t)=exp(−t^(−a)) for t>0, and u_a(t)=0 for t≤0. Choose a fixed ε_a>0 sufficiently small that

\[
\Re(1+w)^{-a}\ge\tfrac12\quad (|w|\le\varepsilon_a).
\]

Cauchy's formula on |z−t|=ε_a t yields, for t>0 and k≥1,

\[
|u_a^{(k)}(t)|\le k!(\varepsilon_a t)^{-k}e^{-t^{-a}/2}
\le C_a^k(k!)^{1+1/a}.
\]

For the second inequality put v=t^(−a), maximize v^(k/a)e^(−v/2), and use (k/e)^k≤k!. The same Cauchy estimate proves that every derivative tends to zero at the origin, so extension by zero is smooth. The k=0 bound is one.

The product u_a(t)u_a(1−t), followed by normalized integration from 0 to t, gives a smooth step supported in the transition interval [0,1], valued in [0,1], with derivative bounds C_a^k(k!)^s after enlarging C_a. Translation, dilation, reflection, and a product of three such one-dimensional cutoffs give box cutoffs χ with

\[
0\le\chi\le1,\qquad |D^\nu\chi|\le(C_a/\ell)^{|\nu|}(|\nu|!)^s.
\]

The normalization is a positive a-dependent constant. It must not be declared uniform in a.

## 2. Chart geometry and telescoping products

Assume frozen G6 with common holomorphic radius h≤1/100 and bound M. Set lattice spacing ℓ=h/16. Retain lattice cubes of radius ℓ/2 intersecting the fixed shell K. For each such cube choose an analytic-chart center x_j in its intersection with K. Put χ_j=1 on the lattice cube of radius ℓ/2, with support inside the cube of radius 2ℓ about the same lattice center. Then the support is at distance at most (5/2)ℓ<h/4 from x_j. In particular it has a positive h-proportional margin inside the chart; Cauchy bounds for the analytic germ F_j hold throughout the support with derivative scale C/h.

At every point at most five lattice centers per coordinate can have that point in their closed radius-2ℓ boxes. Thus support multiplicity is at most L=125, independent of h and the number of boxes. Every derivative of χ_j is zero at a point outside its support, including a support-boundary point where χ_j vanishes, by smoothness and flat extension.

Order the retained boxes arbitrarily and put

\[
\beta_j=\chi_j\prod_{i<j}(1-\chi_i),\qquad G=\sum_j\beta_jF_j.
\]

Each term is extended by zero outside its chart. This is smooth because χ_j is supported a positive distance inside the chart. At a fixed point, only the at-most-L supported χ_j have nonzero jets. All other (1−χ_i) factors have value one and all positive-order derivatives zero. Consequently every Leibniz expansion contains at most L active cutoff factors, even though the written product may have many factors. Only at most L terms β_jF_j have nonzero jets.

The multinomial formula and \(\prod_r k_r!\le k!\) give

\[
\|D^\nu G\|_\infty\le C_a M(C_a/h)^{|\nu|}(|\nu|!)^s.\tag{A1}
\]

The factors L and L^(|ν|) have been absorbed into C_a. They do not depend on cover cardinality. On K at least one χ_j equals one; the telescoping sum of β_j is one. Compatible chart germs therefore make G and its derivatives agree with F on K. Compatibility, or a genuine common analytic function on chart overlaps, is essential here.

## 3. Composition and polynomial estimates

Compose G with coordinatewise cosines on a fixed containing cube to obtain an even smooth periodic function. Gevrey order s in (A1) is preserved with scale C_a/h, not its square. For example, in one variable the Bell-polynomial formula, |D^j cos|≤1, and

\[
\sum_{\substack{l_1+\cdots+l_k=m\\l_1+2l_2+\cdots+kl_k=k}}
\frac{m!}{l_1!\cdots l_k!}
=\binom{k-1}{m-1}
\]

after dropping the factors (j!)^(−l_j), bound the order-k composition derivative by

\[
M k!\sum_{m=1}^k(C_a/h)^m(m!)^{s-1}\binom{k-1}{m-1}
\le M(k!)^s(1+C_a/h)^k.
\]

The displayed combinatorial identity counts ordered compositions of k into m positive parts. Mixed-coordinate derivatives obey the same bound after a dimension-dependent enlargement, or are unnecessary for the one-coordinate Fourier integration used next.

Integrating k times in a coordinate of largest frequency N and choosing k proportional to (hN)^(1/s) yields Fourier coefficients bounded by

\[
C_aM\exp[-b_a(hN)^{1/s}].\tag{A2}
\]

For small hN enlarge C_a. Frequency triples of maximum N number O((N+1)^2); two algebraic-coordinate derivatives of tensor Chebyshev polynomials cost at most C(N+1)^4. Reserving half of (A2) for the tail factor and comparing the rest with an integral gives, for h≤1,

\[
\sum_{N>d}(N+1)^6e^{-b_a(hN)^{1/s}}
\le C_a h^{-7}e^{-(b_a/2)(hd)^{1/s}}.\tag{A3}
\]

Indeed u=hN makes the full moment h^(−7) times a finite a-dependent integral. There is no h^(−7s) loss: the exponential already contains (hN)^(1/s).

Use tensor degree d=⌊q/3⌋, so total ordinary degree is at most q, and average under electron exchange when required. Equations (A2)–(A3) give

\[
\max_{|\nu|\le2}\sup_K|D^\nu(F-Q_q)|
\le C_aM h^{-7}e^{-b_a(hq)^{1/s}}.\tag{A4}
\]

The full absolute weighted coefficient sum is at most C_aMh^(−7), also bounding Q_q and its first two derivatives on the containing cube. Outside the cube, the same Chebyshev growth estimate used in the frozen proof gives, for t=S(y)≥2,

\[
|D^\nu Q_q(y)|\le C_aMh^{-7}(q+1)^4(6t)^q,\qquad |\nu|\le2.\tag{A5}
\]

This bound concerns the very same polynomial in (A4). Small q is absorbed into constants.

## 4. Substitution into the global proof

With h=c_h(1+T)^(−2), replace frozen G7–G8 by (A4)–(A5). Their polynomial prefactor is (1+T)^14, which still dominates the finite-order envelope (1+T)^4 needed in the Poisson lower and upper tails. The unchanged shell summation G18 contributes another (1+T)^4. Thus the total factor replacing (1+T)^66 in G24 is (1+T)^18, and the first exponential becomes

\[
\exp\!\left[-b_a\frac{q^{1/s}}{(1+T)^{2/s}}\right].
\]

The Poisson order and last node remain k=J=256(q+1); the witness remains in exactly V_(769q+770). The outer omitted target is still the actual ψ, as required by G13. The other exponentials and the inner scale in G24 are unchanged.

Choose T=(q+1)^θ with θ=1/(s+2). Then θ<1, so the original large-q node-schedule inequalities still hold. The shell exponent and physical-tail exponent both have power θ; every remaining factor is polynomial in q or decays exponentially in q. Polynomial absorption and the same all-index conversion therefore yield

\[
\inf_{v\in V_n^{(Z)}}\|\psi-v\|_{H^2_*}\le C_a e^{-c_a n^{a/(3a+1)}}.
\]

This conclusion retains G1–G3 as unresolved physical premises. In particular G3 includes the actual H² domain and physical decay. The continuum residual implication additionally needs the actual eigenvalue equation and graph bound; neither is supplied by changing G9. No coefficient-height, rational-arithmetic, termination, or bit-complexity conclusion follows here.

## Provenance

Frozen commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`. Frozen annotated tag: `theorem-t-proof-freeze-2026-09-09`. No frozen artifact was changed.

* `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/GLOBAL_DYADIC_ATTEMPT.md`: SHA-256 `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b`.
* `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/approximation/APPROXIMATION_AUDIT_v1.md`: SHA-256 `53ba43a396ac5bbe7a8a911d6c459df39c0deeab5cc0e31fd8a48b75540f7efe`.
* `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/approximation/RATE_BALANCE_v1.md`: SHA-256 `b50dfd154f52554353794bad7563770525b5cab3e0448e39a0603005b9da91dd`.

Only the scoped replacement and algebraic substitution above were independently assessed in this audit. The earlier approximation audit is used to identify already-reviewed dependencies, not to claim those physical premises proved.
