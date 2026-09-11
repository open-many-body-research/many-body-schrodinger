> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# B1 Fock augmentation decision experiment

**EMPIRICAL.** This directory contains high-precision screening, not an interval
certificate. No new helium enclosure or graph RATE theorem is claimed.

The exact nested dictionary is

\[
V_n=\operatorname{span}\{e^{-2(r+s)}P_{ijk}(r,s,u)
[q\log(r^2+s^2)]^j:j=0,1,\ i+j_{\rm poly}+k+2j\le n\},
\quad q=(r^2+s^2-u^2)/2.
\]

The polynomial indices obey the existing exchange-symmetric basis restrictions
and factorial scaling. The singlet spinor is understood. Power-of-two diagonal
rescalings are rational and recorded separately for each finite computation;
they do not change these nested vector spaces. Dimensions for n=2,...,8 are
8,16,29,47,72,104,145. Basis descriptions have polynomial bit size; optimized
coefficient-height and asymptotic conditioning bounds have not been proved.

**PROVEN (this session), elementary finite admissibility.** The multiplier
q log rho² has k-th derivatives bounded by C rho^(2-k)(1+|log rho|), k≤2,
near the six-dimensional origin. Its Hessian is locally square integrable.
Ordinary distance-polynomial factors introduce only the existing admissible
inverse-distance Hessian singularities; exponential decay controls infinity.
Thus each finite basis element belongs to D(H)=H², with no new regularity theorem.

Depth two was not tested. Its finite terms are admissible, but the existing
C¹,¹ factorization does not establish a nonzero physical quadratic-log-square
coefficient: a fourth-degree log-square contribution may be absorbed in the
remainder. No assertion that fixed log depth is refuted is made.

Let R=r²+s², L=r+s, B=q logR, and let h(P) be the existing exact h_action.
The exact action used in screen.py is

\[
H(e^{-2L}PB)=e^{-2L}\{Bh(P)-(\log R)U-(2qW+8qP)/R\},
\]
\[
U=(q/r)P_r+(q/s)P_s-uP_u-2q(1/r+1/s)P,
\qquad W=rP_r+sP_s+uP_u-2LP.
\]

This follows from ΔB=16q/R and the product rule. The numerical squared-action
matrix integrates the full resulting function; it does not square a projected
Hamiltonian matrix.

The new moment family, with physical rsu incorporated in the exponents, is

\[
\int_{\triangle}e^{-4(r+s)}r^as^bu^c(r^2+s^2)^{-d}
[\log(r^2+s^2)]^h\,dr\,ds\,du,
\qquad a,b,c\ge-1,\ d,h\le2.
\]

Putting S=r+s, t=|r-s|/S and w=u/S produces a radial gamma derivative
at K=a+b+c-2d+2 and a one-dimensional angular integral. LogR equals
2logS+log((1+t²)/2). Gamma derivatives here introduce Euler's constant,
log2 and zeta(2). Angular factors also contain (1+t²)^(-d), powers of
log((1+t²)/2), and either polynomials or -logt after u integration.
Endpoint cancellation is performed algebraically before quadrature: factors
(1-t^q)/(1-t²) become polynomials for even q or a polynomial divided by 1+t
for odd q. The remaining -logt/(1-t²) has its removable endpoint at t=1
handled explicitly. Values do not generally remain in the old
Q+Qlog2+Qpi² representation.

screen.py uses mpmath 1.3.0 at 50 and 70 decimal digits. Candidate selection
uses the common Decimal solver for (Q+10H+25S+tau I)/S with tau=2^-120,
180 inverse iterations, and the strict mean≤-11/4 filter. The requested
additive tolerance is 10^-16, but it is NOT certified: only iteration change,
pencil residual and conditioning proxies are recorded. All returned finite
Decimal coefficients are frozen as exact rational strings. No published
energy participates in selection or acceptance.

At 70 digits, n=2,...,8 Temple-width estimates are approximately
0.01678284448, 0.002253373385, 0.0004245623115, 0.0001294172556,
0.00005609981884, 0.00002063464862, 0.00001008580200.
Every mean passes the strict filter. B1 improves on A throughout this sweep.
B1 beats E at n=2,3,4; E overtakes at n=5 and has a 27.8-fold smaller width
at n=8 (E dimension175, B1 dimension145). This finite comparison is why
the B1 interval-moment implementation was not selected for extension.

The 50→70 digit repeats for n=2,...,6 change widths by at most 2.58e-47.
Six independent polar-coordinate moment evaluations agree within 1.08e-71.
Four direct Cartesian second-derivative H-action evaluations agree within
3.40e-72. These are empirical numerical checks, not directed interval audits.
The 70-digit n7/8 extension took about 81 seconds in total; the largest
single order took about 55 seconds. Exact observed runtimes and machine
details are preserved in the screen JSON files.

diagnostics.json contains full, trailing-five, trailing-four, and hold-last-two
fits for power/exponential/stretched-exponential models against both n and
basis dimension. It separately records the residual at the mean, an empirical
graph residual using the already archived published reference, and the
corresponding shifted-objective excess. That reference enters only this
postprocessing. For graph residual versus n, the best scanned alpha changes
from .07 over the full range to .30 on the last five points and .60 on the
last four. Power-fit q stays around 2.68–2.76. The last-two-point predictions
from a power fit are within 8%; an exponential fit underpredicts by factors
about .66 and .46. This supplies no stable stretched exponent or asymptotic
refutation.

All scripts, exact rational coefficient JSON, high-precision raw G/H/Q tables,
configuration, precision checks and machine-readable fits are included in
manifest.json with SHA-256 hashes. The manifest has an external digest.
Logs are excluded from the manifest because diagnostics writes its log while
generating it. Reproduction uses /usr/bin/python3 and the vendored mpmath:

```sh
/usr/bin/python3 rate_decision/fock/screen.py --orders 2 3 4 5 6 --dps 50
/usr/bin/python3 rate_decision/fock/screen.py --orders 2 3 4 5 6 7 8 --dps 70
/usr/bin/python3 rate_decision/fock/audit.py
/usr/bin/python3 rate_decision/fock/diagnostics.py
```

**OPEN.** A certified interval implementation of these finite new moments,
a physical graph approximation theorem for this dictionary, and polynomial
coefficient/conditioning bounds. The current decision does not require
settling them or asserting that B1 cannot ultimately succeed.
