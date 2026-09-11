> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Arbitrary electron count: precise scope, constructive alternative, and limits

Date: 2026-09-09. This is new post-freeze work. No frozen artifact was changed.

The strongest directly derived results here are the continuum localization and Coulomb-clipping bounds in `GAP_FREE_COMPUTABILITY_v1.md`. They give a gap-free reduction of atomic ground-energy enclosure to a concrete bounded-box enclosure problem. That file supplies a proposed finite algorithm for the box problem, with explicit error bounds. Its implementation and formal verification remain outstanding. This report does **not** mark a uniform polynomial-precision theorem, an N=3 graph approximation theorem, or a verified executable atomic solver as established.

## 1. The input/output problem

Electron count is always **N**; approximation order is **n**. Let N be a nonnegative integer, Z a positive integer (both binary encoded), and p≥1 a requested absolute precision. The precision parameter is measured by its value p, equivalently unary precision, since writing a dyadic answer can require p bits. The numerical uniformity target `poly(N, log(Z+1), p)` is different from polynomial time in the binary length of N, `poly(log(N+1), log(Z+1), p)`.

In atomic units with one fixed infinitely massive point nucleus at the origin, define

\[
\mathcal H_N=\bigwedge^N L^2(\mathbb R^3;\mathbb C^2),\qquad
H_{N,Z}=-\tfrac12\sum_{i=1}^N\Delta_i
-Z\sum_{i=1}^N|x_i|^{-1}
+\sum_{i<j}|x_i-x_j|^{-1}.
\]

The wedge means antisymmetry under simultaneous permutation of space and spin, with Lebesgue measure in space and counting measure in spin. The operator acts componentwise on spin. Its actual continuum domain is `H²(R^(3N); C^(2^N)) ∩ H_N`; its form domain is the analogous H¹ intersection. Define `E(N,Z)=inf spec(H_N,Z)` and `E(0,Z)=0`. An energy named “ground energy” need not be attained by an eigenvector for every N,Z.

Requested output: rational numbers l≤u with `l≤E(N,Z)≤u` and `u−l≤2^(−p)`. Outputting a wavefunction, excited eigenvalues, spin/orbital labels, observable expectations, or deciding binding is a different problem. An algorithm for the complete fermionic energy cannot silently minimize only a selected spin or orbital subspace.

The domain follows from sliced Hardy inequalities and infinitesimal Laplacian relative boundedness; explicit bounds are derived in the companion file. These are classical continuum results, not claimed novel. Kato's original article is [Fundamental properties of Hamiltonian operators of Schrödinger type, 1951](https://doi.org/10.1090/S0002-9947-1951-0041010-X). The original AMS PDF fetch returned HTTP 403 in this audit, so no exact theorem number or unread original wording is attributed to it. The companion proof states the functional-analytic theorem it uses and proves its potential estimates.

## 2. What does and does not follow from the frozen theorem

The frozen `RWA_REPORT.md` §9 explicitly excludes more than two electrons and general many-body tractability. The composition theorem is for each fixed Z and electron count two. Its notation `N=n+2` is an auxiliary approximation variable, not an electron count; it is not reused here.

The exact two-electron trial dictionary uses three scalar distances and exchange-symmetric spatial polynomials multiplied by the spin singlet. For N≥3, a totally symmetric scalar spatial function cannot simply be tensored with a totally antisymmetric N-spin state: `wedge^N C²={0}`. One needs the full spin-space antisymmetry or appropriate matched permutation representations. Even graph density of a new Cartesian Slater basis would not prove the frozen dictionary's stretched-exponential graph rate or its moment-height bounds.

Multiple collisions survive away from total collapse: for N=3, `x1=x2=0`, `x3≠0` has three simultaneous Coulomb poles in its two-electron cluster. An isolated-pair shell cover is therefore not inherited from N=2. A general weighted-analytic theorem must cover a stratification by collision clusters, including nested clusters and their overlaps, and supply constants uniform on the required charts. This file does not discharge that regularity obligation.

## 3. Three distinct complexity statements

| Statement | Required evidence | Status here |
|---|---|---|
| For each fixed N,Z, energy is computable | An effective sequence of certified two-sided continuum enclosures, with eventual width control | Explicit gap-free reduction and proposed bounded-box construction supplied; no verified implementation or Lean theorem |
| For each fixed N,Z, cost is `C_N,Z (p+1)^d_N,Z` | A proved precision rate, representation and coefficient bounds, certified integration, finite-solve and output bit counts | Unresolved; follows conditionally from the hypotheses in §4 |
| Uniform cost polynomial in N, charge input length, p | Uniform control of exponents and constants, dictionary dimension, spin handling, chart counts, integrals, and all relevant spectral data | Unresolved; no such claim follows from fixed-N bounds |

A constant called C_N,Z may grow faster than every polynomial in N or Z. Even `d_N=O(N)` gives `p^O(N)`, not uniform polynomial time. A finite maximum over `2≤Z≤Zmax` does not control an unbounded charge class.

The unitary change of variables y=Zx gives

\[
E(N,Z)=Z^2 e_N(1/Z),\quad
e_N(\lambda)=\inf\operatorname{spec}
\left[-\tfrac12\sum\Delta_i-\sum|y_i|^{-1}
+\lambda\sum_{i<j}|y_i-y_j|^{-1}\right].
\]

To obtain absolute energy error `2^(−p)`, an enclosure for e_N must have width at most `2^(−p)/Z²`. Thus charge scaling adds about `2 log₂ Z` precision bits and moves the analytic constants along the coupling parameter λ=1/Z. Scaling alone does not bound those constants. Shell degeneracies at λ=0 also prevent a casual uniform-gap argument.

## 4. A precise conditional extension of the fixed-shift/Temple route

Fix N,Z and the **actual** H=H_N,Z. Assume the following mathematical and computational premises, each to be proved for a proposed dictionary rather than bundled into an assumed structure:

1. E is an eigenvalue and there is a known rational spectral separator β with `spec(H) ⊆ {E} ∪ [β,∞)` and E<β. The ground eigenspace may have finite multiplicity. Have rational L,U with `L≤E<U<β`, and let g=β−U>0 and σ=L−1.
2. A specified fermionic dictionary W_n⊂D(H) has a normalized ground residual witness of norm at most `C exp(−c n^α)`, for constants C,c>0 and 0<α≤1. This is a continuum graph/residual estimate.
3. Dictionary construction costs `O(n^a)`, its dimension is `O(n^b)`, all moments G,A,Q have certified absolute-entry evaluation cost `O((n+s)^r)` at s fractional bits with integer heights included, and a normalized witness has squared coefficient norm at most `2^h(n)` with a computable bound `h(n)=O(n^q)` dominating matrix/parameter heights.
4. A rational anchor lies in the dictionary and provides the needed fixed upper bound for the shifted reciprocal quotient. Exact rational PSD bisection and negative-witness recovery are implemented with certified rounding of the true moment matrices.

With τ_n=2^(−h(n)−n), additive solve tolerance δ_n=2^(−n), and

\[
J_n(c)=\frac{c^*(Q-2\sigma A+\sigma^2G)c+\tau_n\|c\|^2}{c^*Gc},
\]

the spectral measure argument works without simple ground-state multiplicity. Writing d=E−σ≥1 and η=||(H−E)φ|| gives

\[
\langle H\rangle-E\le\eta^2/g,\qquad
\|(H-\sigma)\phi\|^2-d^2
\le(1+2d/g)\eta^2.
\]

Conversely shifted excess ε implies variance≤ε and mean error≤ε/2. Once ε≤g, the Temple width is at most 2ε/g. Outward interval errors and the strict filter mean≤U are handled as in the frozen composition, with all its premises visible.

Consequently a sufficient order is bounded in terms of

\[
\left[c^{-1}\left(p+\log_+(C(1+d/g))+\log_+(1/g)
+\log_+(1/(U-E))\right)\right]^{1/\alpha},
\]

up to fixed numerical factors and the additive-solve condition. In the same schoolbook binary bit model, put q′=max(1,q) and `B*=max(a,2b+r q′,5b+3q′)`. The conditional precision exponent is `(B*+1)/α` after summing stages. Every symbol a,b,q,r,α,C,c,g,U−E can depend on N,Z. None is proved for an N≥3 analogue of the frozen dictionary here.

An ionization threshold only separates essential spectrum; it need not lie below the first excited discrete eigenvalue. Using E(N−1,Z) as β without excluding bound excitations invalidates the displayed Temple premise. A nonzero spectral gap known merely to exist is not the same as an algorithmically available rational separator. The gap-free alternative in the companion file avoids both requirements, at poor approximation sizes.

## 5. Primary complexity literature and exact applicability

The following are restrictions on claims, not a novelty argument. No search failure is used to infer that a theorem is new.

**O'Gorman–Irani–Whitfield–Fefferman.** [Electronic Structure in a Fixed Basis is QMA-complete, arXiv:2103.08215v1](https://arxiv.org/abs/2103.08215), Theorem 1, Definition 1, and the encoding in the supplied spatial orbitals were inspected in primary full text. The published article is [Intractability of Electronic Structure in a Fixed Basis, PRX Quantum 3, 020322 (2022)](https://doi.org/10.1103/PRXQuantum.3.020322). The restricted problem is QMA-complete at inverse-polynomial promise accuracy; “fixed particle number” means the specified particle-number sector of each instance, with particle number growing in the reduction. The instance-dependent basis carries the encoded problem. It is not one universally fixed constant electron count and not the bottom of the unrestricted continuum atom determined only by N,Z. An algorithm for the latter cannot be applied to arbitrary compressed basis energies without an additional reduction.

**Schuch–Verstraete.** [Computational Complexity of interacting electrons and fundamental limitations of Density Functional Theory, arXiv:0712.0483v2](https://arxiv.org/pdf/0712.0483), published [Nature Physics 5, 732–735 (2009)](https://doi.org/10.1038/nphys1370). The full primary PDF, equation (1), equations (4)–(6), and Supplementary Material §3 were inspected. Its continuum construction uses a designed lattice electric potential and independently varied spin-coupled magnetic fields to encode a Hubbard problem, with inverse-polynomial energy accuracy. The supplementary construction uses delta-well potentials; its remarks identify spin-density DFT and omission of orbital magnetic coupling. This is broader than a spin-independent single point nucleus. It does not establish hardness of the (N,Z)-only class.

For a class that *does* include either reduction, a uniform deterministic classical polynomial-time enclosure algorithm at inverse-polynomial error would decide the corresponding QMA-complete promise problem in P. A precision-polynomial solver suffices because p=O(log s) resolves an inverse-polynomial promise gap for input size s, allowing a constant-factor safety margin. A quantum polynomial-time solver for that general class would analogously put QMA in BQP. These implications require the reduction to fit the solver's exact input class; none is asserted for the point-nucleus atomic class here.

No N-representability, Hubbard, arbitrary-local-Hamiltonian, or thermodynamic-limit undecidability result is substituted for a theorem about finite isolated atoms. Fixed-N computability or fixed-N polynomial precision cost is compatible with growing-N hardness.

## 6. Verification and novelty boundary

Established classical ingredients: fermionic continuum form/domain, Hardy control, variational monotonicity, localization, bounded-potential Galerkin bracketing, and the stated primary hardness results within their classes. The companion file derives the particular explicit bounds used here.

Potentially useful new project artifact: an explicit recursive gap-free enclosure route whose continuum lower bound remains valid even when no N-electron bound state exists. No claim of publication novelty is made; a dedicated literature comparison of this particular construction has not been completed.

Unresolved: all Lean formalization; an audited `BoxEnclose` implementation; actual energy outputs from that implementation; its full bit-cost analysis; a stretched-exponential graph approximation theorem for N=3 or general N with the required symmetry; uniform dependence of regularity constants on collision clusters/N/Z; applicable separators for the Temple route; uniform growing-N efficiency.

## 7. Frozen provenance and read coverage

Frozen root: `THEOREM_T_FREEZE_2026-09-09_212604/`. Commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`. Tag: `theorem-t-proof-freeze-2026-09-09`. SHA-256 values below were checked against `FREEZE_MANIFEST.json` and freshly computed from read-only bytes.

| Frozen relative path | SHA-256 | Coverage for this subtask |
|---|---|---|
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | Entire report, with separate reread of ending §§8–9 after aggregate output truncation |
| `TWO_ELECTRON_THEOREM.md` | `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79` | §§1–3 in full, start of §4, and concluding formal/status ledger and §7; remaining approximation sections are outside this subtask's coverage |
| `rwa_proof/THEOREM_T_COMPOSITION.md` | `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da` | Entire file |
| `CORRECTION_PROTOCOL.md` | `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3` | Entire file |

This scope report finds no frozen claim asserting an arbitrary-N theorem; its extension obligations therefore are not an erratum to a claim the frozen report did not make. Other subtask audits may identify errata in dependencies. A completed version is immutable; revisions must be separate files.
