> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Analyticity from actual factorial Fréchet derivative bounds

This is a fully formalized general analytic implication. Smoothness and
derivative bounds are explicit hypotheses. The theorem does not itself
produce a smooth representative from weak derivatives.

Let \(E,F\) be real normed spaces, with \(F\) complete, let \(\Omega\)
be open, and let \(f:E\to F\) be \(C^\infty\) on \(\Omega\).
Assume \(C\ge0\), \(A>0\), and

\[
\|D^k f(z)\|_{\mathrm{op}}\le CA^k k!
\quad(z\in\Omega,\ k\in\mathbb N).
\]

Define the actual formal multilinear series
\(p_x(k)=(k!)^{-1}D^k f(x)\). For any \(r>0\) such that
\(Ar\le1\) and \(B(x,r)\subset\Omega\), Lean proves
`HasFPowerSeriesOnBall f (factorialFrechetSeries f x) x r`.
In particular, whenever \(\|y\|<r\),

\[
f(x+y)=\sum_{k=0}^\infty\frac{D^k f(x)[y,\ldots,y]}{k!},
\]

with absolute convergence, and the formal series radius is at least \(r\).
The conclusion is an actual power-series representation of \(f\), not
merely convergence of a derivative series to an unspecified function.

If a set \(K\) has a common interior margin \(\delta>0\), meaning
\(B(x,\delta)\subset\Omega\) for every \(x\in K\), one radius

\[
r=\min(\delta,A^{-1})>0
\]

works at every center in \(K\). It is chosen before the center and every
derivative order. Without a common margin, the same hypotheses still give
`AnalyticOnNhd ℝ f Ω`, by choosing a local ball separately at each point.
Neither finite dimension nor completeness of \(E\) is required.

The proof uses the pinned Mathlib theorem
`map_add_eq_sum_add_integral_iteratedFDeriv` from
`Mathlib/Analysis/Calculus/TaylorIntegral.lean`. Its hypothesis is actual
smoothness at all points of the segment. It supplies the integral remainder
after degree \(n\). Bounding its weight by one gives the explicit estimate

\[
\left\|f(x+y)-\sum_{k=0}^{n}\frac{D^k f(x)[y,\ldots,y]}{k!}\right\|
\le C(n+1)(A\|y\|)^{n+1}.
\]

This estimate retains a linear factor in \(n\); no sharper integral-weight
estimate is claimed in this unit. The factor does not reduce the convergence
radius, since \((n+1)q^{n+1}\to0\) for \(0\le q<1\).
Separately, \(\|p_x(k)\|\le CA^k\) proves absolute summability and the
radius bound. The norm remainder limit identifies the sum with \(f(x+y)\).
Absolute summability then converts convergence of the natural partial sums
into Mathlib's unconditional `HasSum` statement.

For a ball-contained increment, the full segment stays inside that ball:
\(\|ty\|\le\|y\|<r\) for \(0\le t\le1\). Thus the result needs
no convexity assumption on the larger set \(\Omega\). At the endpoint
choice \(r=A^{-1}\), the strict increment condition still gives
\(A\|y\|<1\).

The general analytic theorem explicitly assumes actual smoothness and
actual Fréchet operator norm estimates. Its application to a weak Grushin
solution still requires the smooth-representative bridge, identification of
weak jets with classical derivatives, and any conversion of coordinate-word
bounds to operator norm bounds. This unit asserts real analyticity; it does
not prove a complex holomorphic extension, an effective coefficient oracle,
an energy solver, or any complexity bound. No novelty claim is made.

Four new Lean modules contain ten declarations. Exact source/object hashes,
successful compiler logs, the two approved v7 expanded-statement/axiom audits,
and an independent focused review are bound in
`audits/FACTORIAL_FRECHET_ANALYTIC_CHECKPOINT_v1.json`. The official pinned
Lean 4.34.0-rc2 compiler reuses existing pinned dependency objects; this unit
has no isolated source rebuild.

Historical context remains
`THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`,
SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All frozen and prior PASS artifacts are
preserved.
