> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual-eigenfunction RWA and unchanged-dictionary endpoint approximation

Evidence category: **paper theorem composed from explicit weak-PDE
proofs**. The input is an actual continuum eigenfunction on the weak
H2 domain, not a function postulated to have the desired analytic germs.
The theorem does not prove that a ground branch exists, identify it
spectrally, prove its symmetry, or implement an energy algorithm.

## 1. Exact continuum class and local/global analytic conclusions

Fix an integer \(Z\ge2\), \(E\in\mathbb R\), and a real nonzero scalar
\(\psi\in H^2(\mathbb R^6)\) satisfying the actual distributional equation
\[
 \left[-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u\right]\psi=E\psi,
 \quad r=|x_1|,\quad s=|x_2|,\quad u=|x_1-x_2|.                 \tag{A1}
\]
Configuration Hardy makes \(V\psi\in L2\); since \(\psi\in H2\),
the distributional equation is consequently the actual L2
eigenfunction equality required by the component regularity theorems.
Assume simultaneous \(SO(3)\) invariance. The canonical representative
provided by the Lipschitz theorem makes this a pointwise statement;
invariance almost everywhere of the original Sobolev class suffices.
Write
\[
 r=b+c,\quad s=a+c,\quad u=a+b,\qquad
 S=r+s=a+b+2c,\qquad T_{\rm per}=a+b+c.
\]
The physical weight \(S\) and trial dictionary are exactly the original
ones. \(T_{\rm per}\) is only the auxiliary normalized-cover variable.
Put \(a_0=\psi(0)\), using that canonical representative.

The explicit all-N boundedness and Lipschitz proofs, specialized to
\(N=2\), give
\[
 \|\psi\|_\infty\le\mathfrak M_{2,Z,E}\|\psi\|_2,\qquad
 \operatorname{Lip}_{B_1}\psi
                   \le\mathcal L_2\|\psi\|_2.                 \tag{A2}
\]
In the second constant the subscript 2 is the outer-ball radius \(R=2\)
of the Lipschitz theorem, not the particle count. Both constants are
explicit functions of \(Z,|E|\) alone.

Apply the local actual-solution theorem with \(R_{\rm phys}=1\) and
\(\bar\varepsilon=1/4\). It gives constants \(C,h>0\), independent
of \(\psi\) except through its amplitude
\(\Lambda=\operatorname{Lip}_{B_1}\psi+|a_0|\), and compatible
holomorphic extensions of
\(\widehat\psi(\varepsilon\,\cdot)-a_0\) about
\[
 K=\{a,b,c\ge0:T_{\rm per}=1\},
 \qquad |F_\varepsilon|\le C\Lambda\varepsilon
                         \quad(0<\varepsilon\le1/4).           \tag{A3}
\]
In particular the actual physical G1 estimate holds:
\[
 |\partial^\nu(\widehat\psi-a_0)(a,b,c)|
 \le C\Lambda(2/h)^k k!\,S^{1-k},\qquad
 k=|\nu|,\quad0<S<1/4.                                       \tag{A4}
\]
Every \(0<\sigma<1\) version follows by replacing the weight by
\(S^{\sigma-k}\). Boundary derivatives are actual compatible analytic
germ derivatives; agreement only on a normalized surface is not used.

For each fixed \(d_*>0\), the exterior theorem and (A2) give compatible
physical perimetric germs at every \(S\ge d_*\), with radii
\[
 {H_{d_*}\over1+S},\qquad
 \hbox{bound }C_{\infty,d_*}\mathfrak M_{2,Z,E}\|\psi\|_2.        \tag{A5}
\]
This is the actual G2 conclusion. No global L-infinity, local Lipschitz,
analytic coefficient, lifted H12, or boundary-germ assumption remains
to be supplied beyond (A1) and the declared rotation symmetry.
These are still paper deductions, not a Lean composition theorem.

## 2. The exact extracted remainder and its logarithm

For any fixed real number \(\kappa\), define the actual function
\[
 f=-Z(r+s)+u/2,\qquad q=(r^2+s^2-u^2)/2=x_1\cdot x_2,\qquad
 T=r^2+s^2,
\]
\[
 \mathcal R_\kappa=e^{-f}\psi-\kappa a_0q\log T.                \tag{A6}
\]
Then there are explicit \(C_R,A_R>0\), depending on the same data
and \(|\kappa|\), for which
\[
 |\partial^\nu(\widehat{\mathcal R}_\kappa-a_0)|
        \le C_RA_R^k k!\,S^{1-k}\quad(0<S<1/4).                \tag{A7}
\]
Thus it satisfies the original requested RWA weight \(S^{1/2-k}\)
and every fixed weight \(S^{\sigma-k}\), \(0<\sigma<1\).
The original coefficient
\(\kappa_Z=Z(2-\pi)/(3\pi)\) is a permitted choice.

Here is a direct common-neighborhood proof, including the logarithm.
Shrink the radius in (A3) to
\[
 h_R=\min(h,1/128).
\]
On a complex radius-\(h_R\) polydisc about \(K\), each distance has
modulus less than 2, hence \(|f|\le B_f:=4Z+1\) and \(|q|\le6\).
At a real center \(T\ge(r+s)^2/2\ge1/2\) and \(T\le2\).
Complex perimetric displacement \(h_R\) moves each distance by at
most \(2h_R\), so
\[
 |T-T_{\rm center}|\le8h_R+8h_R^2<1/4.
\]
Consequently \(T\) stays in the right half-plane,
\(\operatorname{Re}T>1/4\), \(|T|<3\). The positive-real principal
logarithm exists on the entire neighborhood and satisfies
\[
 |\operatorname{Log}T|\le\log4+\pi/2<4.                       \tag{A8}
\]

For a fixed real \(0<\varepsilon\le1/4\), the actual scaled
remainder difference is represented there by
\[
 G_\varepsilon(z)=
 e^{-\varepsilon f(z)}(a_0+F_\varepsilon(z))-a_0
       -\kappa a_0\varepsilon^2q(z)
                          (2\log\varepsilon+\operatorname{Log}T(z)).
                                                                  \tag{A9}
\]
The equality is on the full real physical neighborhood because
the distances scale linearly and \(q,T\) scale quadratically.
The real logarithm identity uses the strictly positive real scale,
not a choice of a complex scale branch.

Using \(|e^w-1|\le|w|e^{|w|}\), \(|a_0|\le\Lambda\), and
\(\varepsilon|\log\varepsilon|\le1/e<1/2\) for \(0<\varepsilon\le1\),
we obtain
\[
 |G_\varepsilon|
 \le\{e^{B_f}(C+B_f)+30|\kappa|\}\Lambda\varepsilon.             \tag{A10}
\]
The logarithmic part contributes at most
\(6|\kappa a_0|\varepsilon^2(2|\log\varepsilon|+4)
\le30|\kappa a_0|\varepsilon\).
Thus Cauchy on the common radius \(h_R\), followed by the exact
comparison \(T_{\rm per}\le S\le2T_{\rm per}\), proves (A7) with
\[
 A_R=2/h_R,\qquad
 C_R=\{e^{B_f}(C+B_f)+30|\kappa|\}\Lambda .
\]

The fact that every finite \(\kappa\) satisfies this weighted estimate
is significant for the evidence boundary. RWA with weight one does
**not** identify the correct Fock coefficient or prove the stronger
regularity claimed for a particular extracted remainder. Selecting
\(\kappa_Z\) in (A6) reproduces the original RWA function and estimate;
it does not independently verify that coefficient's role in the
separate Fock extraction theorem. Those claims must retain their
own proof and source audit.

## 3. Actual-eigenfunction endpoint approximation, with the tail explicit

Assume in addition that \(\psi\) is exchange symmetric,
\(\|\psi\|_2=1\), and has an actual exponential L2 tail:
\[
 \|\psi\|_{L^2(S>R)}\le C_0e^{-\gamma R}\quad(R\ge1),\qquad
 C_0<\infty,\ \gamma>0.                                      \tag{A11}
\]
The all-N tail-transfer theorem at \(N=2\) then supplies the exact
physical full-Hessian G3 bound, with explicit constants and
exponent \(\gamma/\sqrt2\). Statements (A4), (A5) and this tail
bound discharge every G1–G3 assumption of the sealed endpoint
approximation theorem for this actual eigenfunction.

It follows that the unchanged original dictionary
\[
 V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
       e^{-Z2^jS}\mathcal P_{n-2j}^{\rm sym}(r,s,u)             \tag{A12}
\]
has the paper approximation property
\[
 \boxed{\ \forall n\ge0\ \exists v_n\in V_n^{(Z)}:
       \|\psi-v_n\|_{H^2_*}\le C_Ae^{-c_A n^{1/3}},\quad
                 C_A,c_A>0.\ }                               \tag{A13}
\]
Here \(N=2\) is the electron count, \(n\) the approximation order,
and no computational precision input \(p\) has yet been supplied
to an implemented procedure. The polynomial degree and the dyadic
schedule in (A12) are exactly the original ones.

Tensoring the real spatial approximation with the unit spin singlet
gives the corresponding vector in the full simultaneous spatial-spin
fermionic space, with the same physical H2 norm. The statement applies
to any actual real symmetric rotational eigenfunction with (A11);
it does not require that this eigenfunction be the ground state.
No wavefunction uniqueness is implied.

This is an existence approximation theorem with the explicit physical
PDE inputs stated above. The proof does not give a finite algorithm
for obtaining the \(\psi\)-dependent coefficients from \(Z,n\),
and it does not certify an energy interval. Finite solver correctness,
termination, exact moments, bit complexity and connection to the
actual continuum spectral infimum remain distinct requirements.

## 4. Dependencies and evidence boundary

The following paper arguments, their exact reviews and finite diagnostics
are stored separately. The local/exterior analytic and tail implications
have independent reviews; the local Lipschitz proof and this composition
are being independently checked before sealing.

| Artifact | SHA-256 |
|---|---|
| COULOMB_GLOBAL_BOUNDEDNESS_v1.md | d103aa471fcb626ca330d02a4cfbc6534a038e8827e129cff6c24ef3351377a7 |
| COULOMB_LOCAL_LIPSCHITZ_v1.md | 4429fa7abefc10fc9c0f2c6f3c8c94bf44b424b8c2208539da10017c700d8a78 |
| PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md | 8e65d5d7053012e7b40d891f9a310794aa446f87dde902770a9c13ffe4635f3e |
| EXTERIOR_DISTANCE_ANALYTIC_v1.md | e6fdf92081e37aadd515d7badc65bf632ccfead811b388fc148d169b31183360 |
| COULOMB_H2_TAIL_TRANSFER_v1.md | c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6 |
| ENDPOINT_ONE_THIRD_v3.md | cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a |

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The original RWA target is rwa_proof/RWA_THEOREM.md, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
and the dictionary target is rwa_proof/GLOBAL_DYADIC_ATTEMPT.md,
SHA-256 b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.

This result replaces analytic and boundedness placeholders by direct
actual-solution implications. It retains actual eigenfunction existence,
the advertised symmetry and exponential L2 decay as physical inputs.
Full Theorem T has not been established by this composition.
There is no formal or novelty claim hidden in the word “actual.”
Frozen and sealed successful prior artifacts were preserved.
