> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit constants for the physical exterior tail

**PROVEN — paper proof.** This supplements (P9)–(P11) in
[PHYSICAL_REGULARITY_AUDIT.md](PHYSICAL_REGULARITY_AUDIT.md).
It controls the actual normalized ground state, not a dictionary
approximant. All Sobolev norms below are the physical Cartesian \(H^2_*\)
norm from the leading-singularity theorem.

Fix an integer \(Z\ge2\), and let \(\psi=\psi_Z\). Reuse the established
\(-Z^2\le E_Z\le-Z^2+5Z/8<0\). Set
\[
a=Z/4,\quad K_0=\frac{161\,3^{32}}{159},\quad
L_0=e^a\sqrt{K_0},\quad b=3Z+2,
\]
\[
J_0=\left(Z^2+6aZ+3a+\frac{a^2}{2}\right)L_0,
\quad Q_0=6J_0+(6b^2+2)L_0,
\quad M_0=\left[3+5a^2+(a\sqrt6+a^2)^2\right]^{1/2}.
\tag{X1}
\]
Then for every \(T\ge0\),
\[
\boxed{\|\psi\|_{H^2_*(\{\rho>T\})}\le M_0Q_0 e^{-aT}.}
\tag{X2}
\]
In particular, true physical tails at \(T=n^\alpha\) are compatible with
every fixed stretched-exponential order \(0<\alpha\le1\).

## Proof

The elementary IMS and weighted eigenfunction arguments in (P9)–(P10)
prove
\[
\|e^{a\rho}\psi\|_2^2\le K_0.
\tag{X3}
\]
They require only the physical eigenfunction equation in the Coulomb form
domain, the hydrogenic form bound, and the displayed strict ionization
margin. Their full proof, including the cutoff and weight truncations, is
in the linked audit. No unverified external decay theorem is an input.

For \(F_N=a\min(\rho,N)\), the form identity applied to
\(v_N=e^{F_N}\psi\) gives
\[
\mathfrak h_Z[v_N]\le(E_Z+a^2/2)\|v_N\|_2^2.
\]
All multipliers are bounded and Lipschitz for finite \(N\). From sliced
Hardy, Cauchy–Schwarz and Young,
\[
\mathfrak h_Z[v]\ge\tfrac14\|\nabla v\|_2^2-8Z^2\|v\|_2^2
\quad(v\in H^1).
\tag{X4}
\]
For detail, dropping repulsion bounds the attractions in absolute value
by \(2\sqrt2 Z\|\nabla v\|_2\|v\|_2\). This is at most
\(\|\nabla v\|_2^2/4+8Z^2\|v\|_2^2\), proving (X4).
Since \(E_Z<0\),
\[
\|\nabla v_N\|_2\le\sqrt{32Z^2+2a^2}\sqrt{K_0}.
\]
The product rule therefore yields
\[
\|e^{F_N}\nabla\psi\|_2
\le\left(\sqrt{32Z^2+2a^2}+a\right)\sqrt{K_0}
\le6Z\sqrt{K_0}.
\]
Indeed \(a=Z/4\) and \(32+1/8<(23/4)^2\).
Monotone convergence of the weighted derivative norm gives
\[
\|e^{a\rho}\nabla\psi\|_2\le6Z\sqrt{K_0}.
\tag{X5}
\]

Now take \(\theta=\sqrt{1+\rho^2}\), \(W=e^{a\theta}\).
Since \(\rho\le\theta\le\rho+1\),
\[
\|W\psi\|_2\le L_0,\qquad
\|W\nabla\psi\|_2\le6ZL_0.
\]
The estimates \(|\nabla\theta|\le1\), \(0\le\Delta\theta\le6\) give
\[
|\nabla W|\le aW,\qquad |\Delta W|\le(6a+a^2)W.
\]
Thus \(W\psi\in H^1\), and the distributional product formula gives
\[
H_Z(W\psi)=E_ZW\psi-\nabla W\cdot\nabla\psi
-\tfrac12(\Delta W)\psi,\qquad
\|H_Z(W\psi)\|_2\le J_0.
\tag{X6}
\]
An \(H^1\) vector whose weak Coulomb operator is in \(L^2\) belongs to the
operator domain of the closed form. The established Kato–Rellich domain
identity makes this precisely \(H^2\), so \(W\psi\in H^2\).

For completeness, an explicit graph-to-\(H^2_*\) estimate is
\[
\|v\|_{H^2_*}\le6\|H_Zv\|_2+(6b^2+2)\|v\|_2
\quad(v\in H^2).
\tag{X7}
\]
To prove it, Hardy gives
\[
\|(-Z/r-Z/s+1/u)v\|_2
\le(2\sqrt2 Z+2)\|\nabla v\|_2\le b\|\nabla v\|_2.
\]
Plancherel gives \(d:=\|D^2v\|_2=\|\Delta v\|_2\), while integration
by parts gives \(\|\nabla v\|_2^2\le\|v\|_2d\). Consequently
\[
d\le2\|H_Zv\|_2+2b\sqrt{\|v\|_2d}
\le2\|H_Zv\|_2+\tfrac12d+2b^2\|v\|_2,
\]
and \(d\le4\|H_Zv\|_2+4b^2\|v\|_2\).
Finally,
\(\|v\|_{H^2_*}\le\|v\|_2+\|\nabla v\|_2+d
\le\tfrac32(\|v\|_2+d)\), which implies (X7).
Equations (X6)–(X7) give \(\|W\psi\|_{H^2_*}\le Q_0\).

For \(w=W^{-1}\) on \(\rho>T\),
\[
|w|\le e^{-aT},\quad |\nabla w|\le ae^{-aT},\quad
\|D^2w\|_F\le(a\sqrt6+a^2)e^{-aT}.
\]
Here the six eigenvalues of \(D^2\theta\) have absolute value at most one.
Applying the product rule to \(\psi=w(W\psi)\) bounds its three derivative
norms by \(e^{-aT}\) times the matrix
\[
\begin{pmatrix}1&0&0\\a&1&0\\a\sqrt6+a^2&2a&1\end{pmatrix}
\]
applied to those of \(W\psi\). Its Frobenius norm is \(M_0\), proving (X2).

## What is still open

The exponential decay of \(\psi\) does not bound the tail of a trial
obtained by fitting \(\psi\) on a ball. Degree-\(n\) factors can be large
outside their approximation region. A cutoff of the target, or a
partition of unity between local approximants, is not an element of
\(V_n^{(Z)}\). The preceding estimate therefore does not close Phase 4.
An admissible construction controlling the entire error in the exterior
remains **OPEN**.
