# A certified continuum helium calculation

**PROVEN (paper, with an executed rational/interval certificate).** The calculations in this directory bound the spectral ground energy of the original infinite-mass, nonrelativistic helium operator on the full two-electron fermionic space. They are not a computation of the energy of a boxed or projected physical model. The analytic identification of the integrals and the continuum spectral separator is paper mathematics; the numerical certificate is not a Lean proof.

## The explicit trial family

Write `r=|x₁|`, `s=|x₂|`, `u=|x₁−x₂|`. At integer order Ω, use every triple `i>=j>=0`, `k>=0`, `i+j+k<=Ω`. Define

\[
P_{ijk}(r,s,u)=\frac{u^k}{(i+j+k)!}
\begin{cases}r^is^j+r^js^i,&i>j,\\r^is^j,&i=j.\end{cases}
\]

The unnormalized spatial trial is

\[
F(x_1,x_2)=e^{-2(r+s)}\sum_{ijk}c_{ijk}P_{ijk}(r,s,u).
\]

Every exponent is exactly `2`, the nucleus is exactly at the origin, its charge is exactly `2`, and every coefficient `c_ijk` is a rational number given in the selected `trial_*.json`. Multiply the normalized spatial function by the normalized singlet spinor `(↑↓−↓↑)/sqrt(2)`. The spatial polynomial is exchange symmetric, so the resulting spinor lies in the original antisymmetric Hilbert space. No assumption about the symmetry of the unknown ground state is used to supply the lower bound.

Each basis function is in spatial H². Its weak second derivatives are sums of exponentially decaying polynomially bounded terms and terms bounded near a collision by a constant times `1/r`, `1/s`, or `1/u`. Each squared singularity is locally integrable in its three relative coordinates. First derivatives of distance functions are bounded; mixed products of such first derivatives cause no worse singularity. There are no interface jumps or delta functions, and the exponential controls all polynomial growth at infinity. These observations also cover the intersections of collision sets. Finite rational linear combinations preserve H² membership.

## Exact moments, with the full residual retained

For rotationally invariant integrands, the six-dimensional measure is

\[
8\pi^2rsu\,dr\,ds\,du,
\quad r,s>0,\quad |r-s|\le u\le r+s.
\]

The common factor `8*pi²` is omitted from every computational moment and cancels in every normalized quotient. [The complete derivation](../../archive/v1.0-research-notes/helium_research/helium_method.md) gives the Hamiltonian action and all moment recurrences implemented in [hylleraas.py](hylleraas.py).

In particular, set

\[
I_{abc}(\kappa)=\int e^{-\kappa(r+s)}r^as^bu^c\,dr\,ds\,du.
\]

All moments used satisfy `a,b,c>=−1` and `a+b+c>−3`. With `r=v(1+t)/2`, `s=v(1−t)/2`, `u=vw`, the radial integration gives

\[
I_{abc}(\kappa)=
\frac{2^{-a-b-1}(a+b+c+2)!}{\kappa^{a+b+c+3}}
\int_0^1\big[(1+t)^a(1-t)^b+(1-t)^a(1+t)^b\big]J_c(t)\,dt,
\]

where `J_c(t)=(1−t^(c+1))/(c+1)` for `c>=0`, and `J_(−1)(t)=−log(t)`. Polynomial expansion and endpoint-safe division by `1−t²` reduce every moment exactly to `Q + Q log(2) + Q pi²`. The recurrence never separates divergent endpoint contributions.

The overlap and Hamiltonian entries are rational. Only squared-action moments can need `log(2)` or `pi²`. The checker computes the actual function `HF`, including Laurent terms outside the trial span, and then integrates `(HF)²`. It does **not** square the projected Hamiltonian matrix. The latter would discard the very part of the residual needed for the continuum certificate.

Let `S`, `K`, `Q` denote the norm, energy numerator and squared-action moment, all with the same omitted factor. Then

\[
m=K/S\in\mathbb Q,\qquad
v=Q/S-m^2=\|(H-m)\psi\|_2^2.
\]

Here the second spectral moment is `||Hψ||²`; it needs `ψ∈D(H)=H²`, not `ψ∈D(H²)` for the squared operator. The checker never applies H a second time to its singular first action.

## Certified constants and outward arithmetic

All certificate arithmetic uses Python integers and `fractions.Fraction`, with outward dyadic intervals from the preceding Gaussian stage's [certified_interval.py](certified_interval.py). That module rejects binary-float input. `pi` is enclosed by Machin's identity and alternating arctangent remainder bounds. Squaring its interval encloses `pi²`.

The new logarithm enclosure uses

\[
\log2=2\sum_{n=0}^{K-1}\frac{1}{(2n+1)3^{2n+1}}+R_K,
\quad0<R_K\le\frac{9}{4(2K+1)3^{2K+1}}.
\]

The tail bound follows by replacing each subsequent denominator `2n+1` by `2K+1` and summing the positive geometric series. Coefficient signs are handled by interval multiplication; no apparent cancellation is treated as exact unless it occurs in the rational algebra. Variance is nonnegative by its squared-norm definition, so its lower interval endpoint may validly be intersected with zero.

Candidate construction in [select_trial.py](select_trial.py) or [select_residual_trial.py](select_residual_trial.py) uses high-precision decimal linear algebra. These routines provide **untrusted candidate coefficients**, which are frozen as exact rationals. Their convergence, rounding, choice of shift and reported approximate eigenvalues are not assumptions of the certificate. The checker recomputes all needed continuum moments from those rational coefficients. An arbitrary candidate can fail to give a useful bound without invalidating the checker.

## The continuum lower bound

The full proof in [lower_bounds.md](../../archive/v1.0-research-notes/helium_research/lower_bounds.md) establishes

\[
\sigma(H)\subset\{E_0\}\cup[-5/2,\infty),
\]

with a unique ground eigenvalue below `−5/2`. Briefly, remove the positive electron repulsion. For charge two, the one-electron Coulomb energies begin at `−2` and `−1/2`. Pauli statistics permit a unique `1s↑ ∧ 1s↓` determinant at `−4`; its orthogonal complement for the noninteracting problem lies above `−5/2`. Adding positive repulsion preserves the second min-max bound. A product-orbital trial has exact Rayleigh quotient `−11/4<−5/2`, proving that precisely one level lies below the separator. No numerically estimated excitation energy is used.

For any normalized operator-domain trial with `m<β=−5/2`, the spectral theorem gives

\[
0\le\int(\lambda-E_0)(\lambda-\beta)\,d\nu_\psi
=v+(m-E_0)(m-\beta).
\]

The second moment exists by operator-domain membership. Rearranging and applying the variational principle gives

\[
\boxed{m-\frac{v}{\beta-m}\le E_0\le m.}
\]

The program uses a rational certified upper bound `vplus` and checks `m<β` exactly. It rounds `m−vplus/(β−m)` down and `m` up to rational multiples of `10^(−12)`. Thus every printed decimal endpoint is an exact rational bound. The width test is the exact rational comparison `u−ell<=1/10^6`.

## Meaning of the execution

This gives an a posteriori certificate for a single physical continuum instance. It does not depend on Hylleraas completeness, an extrapolation, an unknown approximation-rate constant, or the unproved uniform Gaussian approximation lemma in the theorem skeleton. It therefore remains valid even if that uniform lemma is false.

Conversely, obtaining this one interval does not prove polynomial precision cost or certify a uniform algorithm for all two-electron molecular geometries. The published helium energy is stored solely for comparison after the certificate has been formed. It is never used as a lower bound, spectral separator, or stopping criterion in the verifier.

The finite-dimensional Hermitian Temple theorem is Lean-checked in `Temple.lean` (a finite-dimensional result not included in this repository; the continuum version is claim S2-001), with scalar interval propagation in `TempleScalars.lean` (not included). The continuum spectral theorem application, exact hydrogen spectrum, coordinate integrations and Python verifier remain outside that formalization. Their proof and execution status is explicitly distinct.
