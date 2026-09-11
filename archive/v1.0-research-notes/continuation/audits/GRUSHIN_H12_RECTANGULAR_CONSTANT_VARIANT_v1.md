> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Smooth rectangular cutoff variant for the H12 one-step input

This records the actual rectangular weak one-step gain consumed by the unchanged 34-gap schedule. It does not assert the full H12 derivative induction or the numerical bound H5. The Lean evidence and immutable source hashes are recorded in `GRUSHIN_H12_RECTANGULAR_ONE_STEP_CHECKPOINT_v1.json`.

The paper input is `GRUSHIN_H12_WEAK_INITIALIZATION_v1.md`, SHA-256 `ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812`. Its H1 permits independent spatial and spectator half-widths. The previously sealed common-width cube family therefore was insufficient for that full input class. The new `rectangularOpenBox` and `grushinRectCutoff` retain the separate four-dimensional Y and three-dimensional T widths. Existing cube sources and seals are unchanged.

Write

\[
\delta=\min(a_Y-b_Y,a_T-b_T)/34>0,\qquad
\Omega_j=\{|y-a_y|_\infty<a_Y-j\delta,\ |t-a_t|_\infty<a_T-j\delta\}.
\]

The actual function is a tensor product of left and right copies of `Real.smoothTransition`. A single pair of finite nonnegative constants \(C_1,C_2\) bounds its scalar first and second derivatives, respectively. The existence proof precedes all centers, widths, gaps, levels, coefficients and solutions. These constants have not been numerically evaluated.

At each outer level \(j\in[0,32]\), put \(r_Y=a_Y-j\delta\), \(r_T=a_T-j\delta\). The energy cutoff has inner half-widths \((r_Y-\delta,r_T-\delta)\) and transition gap \(\delta/2\). The output cutoff has inner widths \((r_Y-2\delta,r_T-2\delta)\) and the same transition gap. Thus the energy cutoff equals one on \(\Omega_{j+1}\), with support in the closed box at level \(j+1/2\); the output cutoff equals one on \(\Omega_{j+2}\), with support in the closed box at level \(j+3/2\). Both are smooth and compactly supported. These are the paper's exact half-gap placements, and the strict margins meet the open-neighborhood hypotheses of the weak energy argument.

For every one of the seven coordinate directions, each cutoff has bounds

\[
|\partial_i\chi|\le4C_1/\delta,
\qquad |\partial_i^2\chi|\le8(C_2+C_1^2)/\delta^2.
\]

No extra factor seven occurs in these individual derivatives: a coordinate direction differentiates exactly one tensor factor. Summing the four Y and three T terms produces the dimension factors in the following actual Grushin coefficients. Let

\[
S=\|a_y\|+2a_Y,\quad
q=(4+3cS^2)(4C_1/\delta)^2,\quad
A=(4+3cS^2)8(C_2+C_1^2)/\delta^2.
\]

For \(c>0\), the output cutoff's combined scalar term is bounded by \(A\); both cutoffs' weighted first-derivative sums are bounded by \(q\). The cutoffs take values in \([0,1]\). The selected compact integration set \(K\Subset\Omega_j\) and auxiliary open set are chosen before the input and source. For raw locally L2 functions \(v,h\) with \(P_cv=h\) in the genuine compact-test weak sense, write

\[
F=\int_K|v|^2,\quad H=\int_K|h|^2,
\quad J=[4A^2+16q(1/2+q)]F+(2+8q)H.
\]

The formal theorem produces \(U=\chi v\) almost everywhere and genuine L2 weak first derivatives \(g_Y,g_T\), together with all ordered Y second derivatives \(h_{YY}\), satisfying

\[
\|U\|_2^2\le F,\quad
\sum_i\|g_{Y,i}\|_2^2\le2F+\tfrac34J,\quad
\sum_j\|g_{T,j}\|_2^2\le J/(16c),\quad
\sum_{i,k}\|h_{YY,ik}\|_2^2\le\tfrac32J.
\]

No weak derivative of the original input is assumed. The outputs are global derivatives of the actual cutoff product; the separately proved inner plateau identifies that product with the original input on the required inner box. The homogeneous companion theorem for a continuous real zeroth-order potential with bound \(b\) substitutes \(H\le b^2F\). It does not claim arbitrary complex-potential formalization.

`h12_scheduled_weak_one_step` composes these facts with the exact min-margin/34 schedule and places the finite constants before every input. The same \(S,\delta,A,q\) work at every scheduled level. `h12_scheduled_inner_plateau` connects each output to level \(j+2\). The geometric schedule proves that the requested target box is contained in level 34 and that two-gap reserves remain through level 32. The intended twelve tangential and five Y-elliptic calls use 24 and 10 gaps, respectively; the differential induction and its full source/coefficient budget remain separate obligations.

The paper's \(24/\delta\) and \(1200/\delta^2\) use its C2 quintic transition, whose scalar derivative bounds are 2 and 15. Those numerical bounds have not been proved for the different `Real.smoothTransition` used here. This is a separately identified smooth-cutoff constant variant. It preserves the paper claim without importing its H3/H4 constants into the new formal theorem. No claim that the old paper constants are false is made.

The subsequent factorial argument `GRUSHIN_FACTORIAL_RECURRENCE_v1.md`, SHA-256 `5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594`, has a further lower-radius condition on Y-cutoff derivative support. Its inherited application is centered at Y=0. The translated upper-radius bound above does not discharge that separate factorial lower bound.

All new proofs use the pinned Lean environment and pre-existing dependency objects. Their expanded statements and kernel axiom dependencies are audited with v5. No source dependency rebuild, numerical constant evaluation, full H12 theorem, factorial conclusion or Theorem T completion is asserted by this checkpoint.
