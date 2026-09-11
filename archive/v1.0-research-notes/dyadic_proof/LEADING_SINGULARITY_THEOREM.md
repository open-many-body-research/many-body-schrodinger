> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# The physical leading logarithm in the exact dyadic dictionary

**PROVEN — paper proof.** This is a local approximation theorem for the actual
leading logarithmic contribution. It is not a theorem about the full ground
state, a normalized residual, or polynomial-time energy computation. No new
Lean theorem or numerical rate experiment is claimed.

## Operator, target, dictionary, and norm

Fix an integer \(Z\ge2\). On spatially symmetric functions in
\(L^2(\mathbb R^3\times\mathbb R^3)\), use
\[
H_Z=-\tfrac12(\Delta_{x_1}+\Delta_{x_2})-\frac Zr-\frac Zs+\frac1u,
\quad D(H_Z)=H^2(\mathbb R^6)\cap L^2_{\mathrm{sym}},
\]
where \(r=|x_1|,\ s=|x_2|,\ u=|x_1-x_2|\). Tensoring with the normalized
spin singlet gives the antisymmetric electronic functions. The operator,
domain, normalized positive ground state \(\psi_Z\), and its strictly
positive value \(\psi_Z(0)\) are the ones established in the preceding
atomic report. In particular, \(\psi_Z\) is a distributional eigenfunction
in \(H^2\); the physical regularity theorems apply to this function.

Set
\[
S=r+s,\qquad \rho^2=r^2+s^2,\qquad
q=x_1\cdot x_2=(r^2+s^2-u^2)/2.
\]
Throughout,
\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
e^{-Z2^jS}\mathcal P_{n-2j}^{\mathrm{sym}}(r,s,u).
\]
The polynomial degree is ordinary total degree, and every power is a
nonnegative integer. We use the physical Cartesian norm
\[
\|v\|_{H^2_*(\Omega)}^2=
\int_\Omega\bigl(|v|^2+|\nabla v|^2+\|D^2v\|_F^2\bigr)\,dx_1dx_2.
\tag{L1}
\]
The Hessian counts ordered mixed derivatives. This norm dominates the usual
multi-index \(H^2\) norm and is equivalent to it by a fixed constant.

The verified physical factorization is
\[
\psi_Z=e^{-ZS+u/2+\kappa_Zq\log\rho^2}\Phi_Z,\qquad
\kappa_Z=\frac{Z(2-\pi)}{3\pi},\qquad \Phi_Z\in C^{1,1}_{\rm loc},
\quad \Phi_Z(0)=\psi_Z(0).
\tag{L2}
\]
It follows from Fournais et al., Theorem 1.1,
[math-ph/0312060](https://arxiv.org/pdf/math-ph/0312060),
DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6),
after \(y_i=2x_i\). The smooth extra factor containing \(\log4\) is absorbed
into \(\Phi_Z\). The rescaling and actual remainder extraction are proved in
[PHYSICAL_REGULARITY_AUDIT.md](PHYSICAL_REGULARITY_AUDIT.md), (P1)–(P4).
Thus the target here is precisely
\[
a_Z=\kappa_Z\psi_Z(0),\qquad
f_{\log,Z}=a_Z e^{-ZS+u/2}q\log\rho^2.
\tag{L3}
\]
This retains both the nonradial quadratic factor and the physical cusp
multiplier. The identity
\[
\psi_Z=f_{\log,Z}+e^{-ZS+u/2}\mathcal R_Z,\qquad
\mathcal R_Z\in C^{1,1}_{\rm loc},
\]
is an actual local extraction, not an assumed full Fock series.
We compare on a ball; there is no cutoff in any dictionary witness.

## Theorem and explicit constants

Define
\[
M_d(Z)=\left[\frac{8\pi^2}{15}
 \frac{(2d+5)!}{(2Z)^{2d+6}}\right]^{1/2},\quad d=0,1,2,
\]
\[
C_{\rm ang}=64M_0+(2+8Z)M_1+(1+Z+Z^2)M_2,\qquad
D_{\rm ang}=63\cdot10^6\cdot17^8\cdot11^{11}Z^{-3},
\]
\[
A_{\rm rad}=2^{43}(1+\log Z)Z^{-3},\qquad
A_{\rm ang}=9C_{\rm ang}+2D_{\rm ang},
\]
\[
K_Z=2(A_{\rm rad}+A_{\rm ang}),\qquad
B_Z=10^7(1+\log Z)Z^{-3}+5C_{\rm ang}.
\tag{L4}
\]
For every radius \(0<D\le1/\sqrt2\) inside the local factorization
neighborhood and every integer \(n\ge0\), there is an explicit
\(g_n\in V_n^{(Z)}\subset D(H_Z)\) such that
\[
\boxed{
\|f_{\log,Z}-g_n\|_{H^2_*(B_D)}
\le C_{\log}(Z,D)\,2^{-n/104},\qquad
C_{\log}(Z,D)=10|a_Z|e^{D/\sqrt2}(K_Z+B_Z).
}
\tag{L5}
\]
All \(Z\)-dependent constants in this estimate are displayed. The fixed
physical amplitude \(\psi_Z(0)\) occurs explicitly. Its numerical
computability is not presumed by this existence/approximation theorem.

Writing \(\delta=D/2\), the same witnesses satisfy
\[
\|e_n\|_{L^2(B_\delta)}+\|H_Ze_n\|_{L^2(B_\delta)}
\le G(Z,\delta)C_{\log}(Z,2\delta)2^{-n/104},
\tag{L6}
\]
where \(e_n=f_{\log,Z}-g_n\) and
\[
G(Z,\delta)=1+\sqrt6/2+(4Z+2)(1+\delta^{-1}).
\]
For the local shifted operator one may instead use
\[
\|(H_Z-E_Z)e_n\|_{L^2(B_\delta)}
\le [|E_Z|+\sqrt6/2+(4Z+2)(1+\delta^{-1})]
C_{\log}(Z,2\delta)2^{-n/104}.
\tag{L7}
\]
This remains an error for one extracted component. It is not the target
\(\|(H_Z-E_Z)\phi_n\|\) for a normalized approximation to \(\psi_Z\).

## 1. Combine the actual radial and angular components

The exact identity is
\[
\log\rho^2=2\log S+2\log(\rho/S),\qquad
\log(\rho/S)=-\frac12\sum_{k=1}^\infty
\frac1k\left(\frac{2rs}{S^2}\right)^k,\qquad
0\le\frac{2rs}{S^2}\le\frac12.
\tag{L8}
\]
The complete component proofs, including their Cartesian weak derivatives,
are [DYADIC_RADIAL_LEMMA.md](DYADIC_RADIAL_LEMMA.md), (R1)–(R10), and
[ANGULAR_LEMMA.md](ANGULAR_LEMMA.md), (A1)–(A14).
We recall the constructions sufficiently to specify the witness.

For the radial component at index \(N\ge4\), take
\[
J=\lfloor N/4\rfloor,\quad p=N-2J-2,\quad \lambda_j=Z2^j,
\quad I_j=[3\lambda_j/4,3\lambda_j/2]\ (j\ge1),
\]
\[
c_Z=\int_0^{Z/2}\frac{e^{-t}-1}{t}\,dt+
\int_{Z/2}^\infty\frac{e^{-t}}t\,dt,\qquad
P_p(S)=\sum_{k=1}^p\frac{(-1)^{k+1}(Z/2)^kS^k}{k\,k!},
\]
\[
w_{jk}=\frac{(-1)^k}{k!}
\int_{I_j}\frac{(\lambda-\lambda_j)^k}{\lambda-Z}\,d\lambda,
\quad
R_N=q\left[e^{-ZS}(c_Z+P_p(S))-
\sum_{j=1}^J e^{-\lambda_jS}\sum_{k=0}^p w_{jk}S^k\right].
\tag{L9}
\]
Set \(R_N=0\) for \(N<4\). The radial proof gives, for \(N\ge4\),
\[
\|qe^{-ZS}\log S-R_N\|_{H^2_*}
\le 2^{42}Z^{-3}2^{-N/4}.
\]
Here and in the rest of this section norms are global on \(\mathbb R^6\).
For the small indices, (R2), (R9) with \(d=1\), and (R10) give
\[
\|qe^{-ZS}\log S\|_{H^2_*}
\le Z^{-3}\left[3000(2+\log Z)+4\,665\,600+889\right]
\le5\cdot10^6(1+\log Z)Z^{-3}.
\tag{L10}
\]
For the tail bound in (L10), use \(\lambda-Z\ge\lambda/3\) on
\(\lambda\ge3Z/2\). The head integral is bounded by
\(1200\cdot6^5Z^{-3}\int_0^{Z/2}(t/Z)\,dt/t\).
Consequently, for all \(N\ge0\), the radial error is at most
\(A_{\rm rad}2^{-N/52}\).

For the angular component at index \(N\ge28\), let
\[
m=\lfloor(N-2)/26\rfloor,\quad K=m,\quad P=16m,\quad J=4m,
\quad I_0=[Z,3Z/2],
\]
and use the same \(I_j,\lambda_j\) as above. Define
\[
A_N=-\sum_{k=1}^{K}\frac{2^{k-1}q(rs)^k}{k(2k-1)!}
\sum_{j=0}^{J} e^{-\lambda_jS}
\sum_{b=0}^{P}\frac{(-S)^b}{b!}
\int_{I_j}(\lambda-Z)^{2k-1}(\lambda-\lambda_j)^b\,d\lambda.
\tag{L11}
\]
Set \(A_N=0\) for \(N<28\). These are rational coefficients, and
\[
\|qe^{-ZS}\log(\rho/S)-A_N\|_{H^2_*}
\le A_{\rm ang}2^{-N/52},\qquad
\|qe^{-ZS}\log(\rho/S)\|_{H^2_*}\le5C_{\rm ang}/2.
\]
The inverse powers in (L8) were eliminated by
\[
e^{-ZS}S^{-2k}
=\frac1{(2k-1)!}\int_Z^\infty
(\lambda-Z)^{2k-1}e^{-\lambda S}\,d\lambda,
\]
followed by Taylor expansion about exactly the allowed \(\lambda_j\).
The integrals in (L11) are polynomial integrals over rational endpoints.
Every final polynomial has degree \(2+2k+b\), and the maximum consumed
index is \(2+2K+P+2J=26m+2\le N\).
The proof controls angular, Taylor, and omitted-scale errors in the full
physical \(H^2_*\) norm, uniformly in \(k\), not merely for a fixed angular
order. The inequalities \(72(2/3)^{16}<1/8\) and
\(32\,2^{-12}=2^{-7}\) absorb the growth of those constants.

Define
\[
F_Z=qe^{-ZS}\log\rho^2,\qquad b_N=2(R_N+A_N)\in V_N^{(Z)}.
\]
Equations (L8)–(L11) prove the global estimates
\[
\|F_Z-b_N\|_{H^2_*}\le K_Z2^{-N/52},\qquad
\|F_Z\|_{H^2_*}\le B_Z.
\tag{L12}
\]
Both sums use the same dictionary index \(N\); adding them does not add
their degree budgets.

## 2. Include the physical electron–electron cusp multiplier

Let \(d=D/\sqrt2\le1/2\), \(A=e^d\), and
\[
T_L(u)=\sum_{\ell=0}^L\frac{(u/2)^\ell}{\ell!}.
\]
On \(B_D\), \(u/2\le d\). The scalar derivatives satisfy
\[
|T_L|\le A,\qquad |T_L'|\le A/2,\qquad |T_L''|\le A/4.
\]
For \(u>0\),
\[
|\nabla u|=\sqrt2,\qquad \|D^2u\|_F=2\sqrt2/u.
\]
The sliced three-dimensional Hardy inequality gives
\[
\|v/u\|_{L^2(\mathbb R^6)}\le2\|\nabla_1v\|_2
\le2\|\nabla v\|_2,\qquad v\in H^1(\mathbb R^6).
\]
Hence, for any global \(v\in H^2\), the three local product norms are
bounded by the following matrix applied to the three global norms:
\[
\begin{pmatrix}
\|T_Lv\|_2\\ \|\nabla(T_Lv)\|_2\\ \|D^2(T_Lv)\|_2
\end{pmatrix}_{B_D}
\le
A\begin{pmatrix}
1&0&0\\1/\sqrt2&1&0\\1/2&3\sqrt2&1
\end{pmatrix}
\begin{pmatrix}\|v\|_2\\\|\nabla v\|_2\\\|D^2v\|_2\end{pmatrix}_{\mathbb R^6}.
\]
Its Frobenius norm is \(\sqrt{87/4}<5\), proving
\[
\|T_Lv\|_{H^2_*(B_D)}\le5A\|v\|_{H^2_*(\mathbb R^6)}.
\tag{L13}
\]
This is a local estimate; a uniform bound for multiplication on all of
\(\mathbb R^6\) is neither used nor claimed.

For \(L\ge2\), write \(Q_L=e^{u/2}-T_L(u)\). Taylor's series gives
\[
|Q_L^{(j)}|\le 2^{-j}t_L\quad(j=0,1,2),\qquad
t_L=A\frac{d^{L-1}}{(L-1)!}\le A2^{1-L}.
\]
Applying the identical Hardy/product argument to the explicit global
\(F_Z\) gives
\[
\|Q_LF_Z\|_{H^2_*(B_D)}\le5t_LB_Z.
\tag{L14}
\]
The weak derivatives at \(u=0\) are legitimate: the \(1/u\) Hessian is
locally square integrable in three relative coordinates, and the distance
function has no surface delta in its weak second derivatives.

For \(n\ge4\), set
\[
N=\lfloor n/2\rfloor,\qquad L=\lceil n/2\rceil,\qquad
g_n=a_ZT_L(u)b_N.
\tag{L15}
\]
Multiplication adds exactly \(L\) to the polynomial degree and introduces
no new exponents. A term at block \(j\) has degree at most
\(N-2j+L=n-2j\). Therefore \(g_n\in V_n^{(Z)}\).
It is globally in the operator domain: every finite distance polynomial
times a positive decaying exponential has locally square-integrable
Cartesian Hessian, including all three pair sets, and integrable tails.

By (L12)–(L14),
\[
\|f_{\log,Z}-g_n\|_{H^2_*(B_D)}
\le5|a_Z|A\left[K_Z2^{-N/52}+B_Z2^{1-L}\right].
\]
Now \(2^{-N/52}\le2\,2^{-n/104}\) and
\(2^{1-L}\le2\,2^{-n/104}\), proving (L5) for \(n\ge4\).
For \(n<4\), take \(g_n=0\). The same product estimate gives
\(\|f_{\log,Z}\|_{H^2_*(B_D)}\le5|a_Z|AB_Z\), which is bounded by
the right side of (L5). This proves every claimed index, including zero.

## 3. Local graph estimate and its limits

For a function \(v\in H^2(B_{2\delta})\), use a Lipschitz cutoff equal to one
on \(B_\delta\), zero outside \(B_{2\delta}\), with gradient bounded by
\(\delta^{-1}\), only to apply Hardy to \(v\). Each of \(r,s,u\) then obeys
\[
\|v/r\|_{B_\delta},\ \|v/s\|_{B_\delta},\ \|v/u\|_{B_\delta}
\le2\bigl(\|\nabla v\|_{B_{2\delta}}
+\delta^{-1}\|v\|_{B_{2\delta}}\bigr).
\]
The trace inequality gives
\(\|\Delta v\|_{B_\delta}\le\sqrt6\|D^2v\|_{B_{2\delta}}\).
The triangle inequality proves (L6) and (L7). The cutoff is not multiplied
into \(g_n\), and no boundary condition is imposed on \(v\).

## Coefficients, adversarial checks, and scope

The angular witness has rational coefficients with polynomial bit length,
as proved in its component file. The radial coefficients are finite
rational-plus-rational-log expressions and one fixed real constant \(c_Z\);
their magnitude logarithms and rational-factor heights are polynomial in
the index. The multiplier coefficients \(1/(2^\ell\ell!)\) have
\(O(n\log(n+2))\) bit length. Their products and the polynomially many sums
preserve polynomial height accounting for rational factors. The fixed
amplitude \(a_Z\) does not need to be computed for this local theorem.
This is a real-coefficient approximation witness, not a rational
certificate of the ground energy.

The independent audit checked the two component estimates, increasing
angular order, all scale tails, exact degree use, the multiplier matrix,
the radius \(D\) versus \(D/2\), and the \(|E_Z|\) term in the shifted local
bound. Pair axes and collinear configurations are included in the Cartesian
estimates. No forbidden reciprocal basis element survives. The preceding
fixed-finite-exponent obstruction cannot be applied with uniform constants
to the present expanding exponent set.

Nothing here estimates the nonconstant \(\mathcal R_Z\) at all derivative
orders, joins its pair neighborhoods by an admissible global dictionary
construction, controls the exterior extrapolation of that construction,
or proves proximity of \(g_n\) to the normalized ground state. Thus the
leading-singularity gate is **PROVEN**, while the ground-state RATE and
Theorem T remain **OPEN**.
