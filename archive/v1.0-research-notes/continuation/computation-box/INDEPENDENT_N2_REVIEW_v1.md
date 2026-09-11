> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the two-electron single-determinant box stage

Date: 2026-09-09. Evidence: **paper/code review and independent finite exact checks**, not Lean verification. Reviewed source `exact_two_electron_stage_v1.py` has SHA-256 `8f5688e38d89b9cf75ebb8257edf339c12a1bb7a231d71f638e8978246e174b4`; its primitive source `exact_box_v1.py` has SHA-256 `f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58`. Later source changes require separate reconciliation.

The frozen baseline is `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`, SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. This is a separate continuum-box trial computation, not an implementation of the frozen exponential-polynomial dictionary.

No invalid bound was found in this source. The result is a finite-stage enclosure for the actual N=2 Dirichlet spectral infimum, based on standard continuum form theorems and the written estimates below. Increasing the integration grid at fixed compression dimension does not establish a total arbitrary-precision N=2 box solver.

## Actual fermionic trial and kinetic complement

Write Ω=(-2R,2R)^3, R≥1, and let φ be the normalized real (1,1,1) Dirichlet sine orbital. The two spin orbitals φ↑ and φ↓ are orthonormal. Their normalized wedge is

\[
\Psi(x_1,s_1,x_2,s_2)=\phi(x_1)\phi(x_2)
 \frac{\mathbf1_{s_1=\uparrow,s_2=\downarrow}
       -\mathbf1_{s_1=\downarrow,s_2=\uparrow}}{\sqrt2}.
\]

The spin sum of |Ψ|² is exactly |φ(x₁)|²|φ(x₂)|². Therefore the one-body nuclear expectation is counted twice, while the sole pair interaction is counted once. There is no missing exchange integral: the spin orbitals are orthogonal and the spatial factor is symmetric. The vector is normalized and antisymmetric under simultaneous spatial/spin exchange. Its form kinetic energy is

\[
T_{\rm trial}=\frac{6\pi^2}{32R^2}.
\]

The two lowest one-particle spin orbitals span a two-dimensional space. Its fermionic second exterior power has dimension one and is precisely the displayed trial. Hence the full N=2 fermionic kinetic ground eigenspace is exactly the rank-one compressed subspace P, not a hidden restriction to a chosen spin sector. In its orthogonal complement at least one occupied one-particle orbital has spatial indices beyond (1,1,1). The next spatial kinetic energy has squared-index sum 6. Thus

\[
QTQ\ge\frac{(3+6)\pi^2}{32R^2}Q.
\]

The code uses the lower rational π endpoint in this expression. This is a lower bound on the *full fermionic* complement. The projection commutes with the kinetic operator. Dirichlet extension by zero to full space is used at form level (H¹), not as an H² extension through the box boundary.

## Exact grouping of the six-dimensional interaction integral

The orbital probability density factors over the three coordinates. For one coordinate let w_j be its probability in cell j of a uniform J-cell partition. If X and Y are independent with that density, the probability of the cell-label difference d≥0 is

\[
s_d=\sum_{j=d}^{J-1}w_jw_{j-d}.
\]

The probability for −d equals that for d by interchanging the two labels; no spatial reflection assumption is needed for this identity. For d=0 count the term once and for d>0 count it twice. Coordinate independence gives the product of these weights over three coordinates and the multiplicity 2 to the power of the number of nonzero coordinate differences.

With h=4R/J, a nonnegative cell-label difference d confines the actual coordinate difference to h[d−1,d+1]. Thus the distance squared for a difference triple obeys

\[
h^2\sum_a\max(d_a-1,0)^2
\le|X-Y|^2\le h^2\sum_a(d_a+1)^2.
\]

This includes equal and adjacent cells, where the lower distance is zero. Since min(1/r,M) is decreasing and nonnegative, the code's potential interval encloses it over every cell pair in the group. All probability intervals are nonnegative, so multiplying them and summing gives an enclosure of the actual clipped interaction integral. The reduction from J⁶ to J³ potential evaluations plus O(J²) one-coordinate probability products is an exact regrouping with an explicit within-cell potential enclosure, not an unbounded midpoint approximation.

The one-body nuclear routine uses the correct analogous cell probability integrals and reflection multiplicities. Each probability uses the normalized sine-square integral already checked in the N=1 review. This gives an interval for a single positive inverse-radius expectation. The compressed energy interval is therefore exactly the outward evaluation of T_trial−2Z·nuclear+pair.

## Complement bound and lower bounds

For
\[
V_M=-Z\{\min(1/r_1,M)+\min(1/r_2,M)\}
       +\min(1/r_{12},M),
\]
the triangle bound ||V_M||≤B=M(2Z+1) is conservative and valid. The only P/Q cross term is the bounded potential. For η>0,

\[
2|\langle u,V_Mv\rangle|
\le\eta\|u\|^2+B^2\|v\|^2/\eta,
\]

so the lower clipped endpoint is the minimum of the compressed lower endpoint minus η and Λ−B−B²/η. Both the clipped and uncut forms are ≥−Z²: nuclear clipping weakens attraction, pair clipping remains nonnegative, and summing the two one-electron square-completion inequalities gives −2·Z²/2. Taking the maximum with −Z² is therefore justified.

## The common upper bound and both clipping directions

For any normalized H¹₀ fermionic vector, the positive nuclear and pair clipping differences satisfy

\[
0\le D_{\rm nuc}\le(2Z/M)T,
\qquad0\le D_{\rm pair}\le T/M,
\qquad q-q_M=-D_{\rm nuc}+D_{\rm pair}.
\]

Consequently |q−q_M|≤δT with δ=(2Z+1)/M. There is no one-sided ordering of q and q_M in this N=2 case. On the explicit trial, however,

\[
q[\Psi]\le q_M[\Psi]+T_{\rm trial}/M.
\]

The source's `direct_trial_upper` is therefore a true uncut upper bound. It is also a clipped upper bound because its added kinetic term is positive.

The coarse constant 5 is independently valid for both forms. Dropping attraction, the pair Hardy bound gives q[Ψ],q_M[Ψ]≤T_trial+2√T_trial. Since π²<10 and R≥1, T_trial<15/8. The inequality 2√t≤t+1 gives T_trial+2√T_trial≤2T_trial+1<19/4<5. Thus the minimum U of 5 and `direct_trial_upper` is a common upper bound for λ and λ_M.

Both forms satisfy q,q_M≥T/2−2Z². Their normalized minimizing vectors therefore have kinetic energy at most K₀=2(U+2Z²). Compactness of the bounded-domain form embedding supplies such minimizers; normalized approximate minimizers would also suffice after taking a limit. Evaluate q_M at a q-minimizer to prove λ_M≤λ+δK₀, and evaluate q at a q_M-minimizer to prove λ≤λ_M+δK₀. This proves the two-sided restoration interval.

The source lower endpoint max(−Z², clipped_lower−δK₀) and upper endpoint min(U, clipped_upper+δK₀) are therefore both valid. The full-space interval [−Z²,min(0,box_upper)] follows from the full-space lower bound, zero-extension of form trials, and separated/dilated fermionic trials proving E≤0. It does not use a ground-state gap or exact ground eigenfunction.

## Independent executed checks and limits

The source `independent_n2_checks_v1.py` computes the interaction interval independently by explicit enumeration of all J⁶ physical cell pairs. It derives relative distance bounds from the individual physical cell endpoints; it does not call the grouped difference weights. It writes only to stdout and can be rerun without modifying the saved receipt.

```sh
python3 -B THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/computation/box/independent_n2_checks_v1.py
```

The exclusively created receipt `independent_n2_checks_v1.json` records exact equality of the resulting rational intervals with the grouped source for eight cases: J=1,2,3,4, each with (R,M)=(1,3) and (2,1/32), totaling 9,780 explicit six-dimensional cell pairs. In the latter cases the clipped potential is exactly 1/32 everywhere, because the maximum relative radius is 8√3<32; every interval also contained that exact normalization value.

The independent enumeration shares the previously reviewed interval primitives. It is a finite test of grouping, multiplicity, normalization and distance bounds, not a second verified arithmetic kernel. Neither it nor this paper review proves the Python runtime, formal continuum linking, arbitrary-precision N=2 termination, the original Theorem T, or a useful precision rate. The rank-one stage keeps a fixed infinite-dimensional complement estimate and must not be advertised as a convergent Galerkin hierarchy.
