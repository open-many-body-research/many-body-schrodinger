> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact R25 conversion and the conditional order-uniform bound

The numerical conversion is a fully formal scalar theorem. The subsequent
factorial estimate is a conditional scalar implication: it retains the
actual fixed-gap recurrence as a premise and, where used, the explicit
order-shift comparison representing the still-separate R24 application.

For every natural \(k\), the proposed constants satisfy

\[
(k+12)^{k+11}\le 3^{12}12^{11}6144^k k!.
\]

A proof covering \(k=0\) without a separate division argument starts with
the exponential-series term inequality

\[
\frac{(k+12)^k}{k!}\le e^{k+12}\le3^{k+12}.
\]

Also \(k+12\le12(k+1)\le12\,2^k\). Split the power into
orders \(k\) and \(11\), multiply these two estimates, and use
\(3\,2^{11}=6144\). Thus the stated constants are justified without
using a Stirling approximation. They are deliberately coarse; no sharpness
claim is made.

Let the hypotheses of the sealed scalar fixed-gap theorem hold:
\(0<\rho\le1\), \(C,A\ge1\), \(F,H_0\ge0\), and a profile
\(N_r(s)\) that is nonnegative and nonincreasing in \(s\in[0,\rho]\),
bounded by \(H_0\) for \(r\le8\), and satisfies the explicit R18
recurrence for every \(r\ge9\) and admissible gap. Put

\[
B=2CA,\qquad S=F+H_0,\qquad D=2B/\rho.
\]

The sealed result applied at order \(r=k+11\) gives

\[
N_{k+11}(\rho)\le 2BS D^{k+11}(k+12)^{k+11}.
\]

Combining this with the proved numerical inequality yields

\[
N_{k+11}(\rho)
\le \bigl(2BD^{11}3^{12}12^{11}\bigr)S(D\,6144)^k k!.
\]

For any \(E_{\rm box}\ge0\) and scalar family satisfying the explicit
comparison \(W_k\le E_{\rm box}N_{k+11}(\rho)\), it follows that

\[
W_k\le C_* S A_*^k k!,\qquad
C_*=2BE_{\rm box}D^{11}3^{12}12^{11},\quad A_*=D\,6144.
\]

These are exactly the R1 constants after identifying the separately supplied
base norm \(H_0=498WH\). The formal theorem does not assert that identity
or the physical base estimate. It also provides the pointwise-family version
when \(\|J_k(x)\|\le E_{\rm box}N_{k+11}(\rho)\) is supplied for
every \(x\) in a specified set. The constants precede both \(k\) and
\(x\), and the same statement covers \(S=0\).

No derivation of the raw weighted PDE recurrence, Sobolev embedding,
identification of the family as actual derivatives, or physical analytic
approximation is included. Neither these real inequalities nor their Lean
proofs supply an executable energy solver or a bit-complexity theorem.

The final source roots are in `lean/GrushinScalarFactorialBound_v1.lean`;
the numerical theorem is in `lean/GrushinShiftedPowerFactorial_v1.lean`.
Exact compilation and approved v7 expanded-statement/axiom audit records
are bound in `audits/GRUSHIN_SCALAR_FACTORIAL_CONVERSION_CHECKPOINT_v1.json`.
The official pinned Lean 4.34.0-rc2 compiler reuses existing pinned dependency
objects; this unit does not include an isolated source rebuild.

This is a continuation of `audits/GRUSHIN_FACTORIAL_RECURRENCE_v1.md`,
R23–R25. The frozen context remains
`THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`,
SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All frozen and prior PASS bytes are
preserved. No novelty claim is made.
