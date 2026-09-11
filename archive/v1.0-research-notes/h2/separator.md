> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# A continuum separator for neutral H₂ at R = 7/5

**Status.** The separator \(\beta=-91/50=-1.82\) Hartree is proved within the spatial symmetric, inversion-even sector, using paper mathematics and executed rational interval arithmetic. Positivity identifies that sector's ground energy with the full spin-fermionic ground energy. This does **not** assert that the full spin-fermionic operator has only one eigenvalue below \(-1.82\). No continuum theorem here is Lean checked.

All energies are **electronic**, with infinite nuclear masses, charges 1, and separation exactly \(7/5\) bohr. The nuclear-repulsion constant \(5/7\) is omitted. The one-electron moment certificate is h2/slater_moments.py; its exact endpoints and successful log are h2/slater_moments.json and h2/slater_moments.log. The JSON has no floating-point numbers. Integer/rational arithmetic, outward interval operations, and proved series remainders enter the assertions. Elapsed time appears only in the log.

Existence and physical-ground identification additionally need a spatial symmetric, inversion-even two-electron trial with mean below \(-1.82\). This explicit hypothesis is discharged by any separately certified molecular trial satisfying it.

## Operators and sectors

Put \(A=(0,0,-7/10)\), \(B=-A\), \(r_C(x)=|x-C|\). On \(\mathfrak h=L^2(\mathbb R^3;\mathbb C)\), define
\[
h=-\tfrac12\Delta-r_A^{-1}-r_B^{-1},\qquad D(h)=H^2(\mathbb R^3).
\]
The form domain is \(H^1(\mathbb R^3)\). Hardy and Kato–Rellich give this self-adjoint realization. Inversion \(If(x)=f(-x)\) commutes with \(h\). Let \(\mathfrak h_g=\ker(I-1)\), \(\mathfrak h_u=\ker(I+1)\), and \(h_g,h_u\) be the self-adjoint restrictions.

The scalar two-electron operator is
\[
H_{\rm sc}=h_1+h_2+|x_1-x_2|^{-1},\qquad D(H_{\rm sc})=H^2(\mathbb R^6).
\]
Let \(\mathcal K\) consist of functions invariant under exchange \(x_1\leftrightarrow x_2\) and simultaneous inversion \((x_1,x_2)\mapsto(-x_1,-x_2)\). This closed subspace reduces \(H_{\rm sc}\); denote its restriction by \(H_{\mathcal K}\).

The physical fermionic space is the simultaneous-exchange antisymmetric subspace of \(L^2((\mathbb R^3\times\{\uparrow,\downarrow\})^2)\), with counting measure on spin. Its operator domain is spatial \(H^2(\mathbb R^6;\mathbb C^4)\) intersected with that subspace. An exchange-symmetric spatial function times the normalized antisymmetric spin singlet is fermionic.

## Exact one-electron spectral indexing

For \(C=A,B\), define
\[
k_C=-\tfrac12\Delta-2/r_C,\quad
\phi_C=(8/\pi)^{1/2}e^{-2r_C},\quad P_C=|\phi_C\rangle\langle\phi_C|.
\]
The exact charge-2 hydrogenic spectrum gives
\[
k_C\ge-\tfrac12I-\tfrac32P_C:
\]
its ground energy is \(-2\), with one spatial eigenfunction, and the remaining spectrum is at least \(-1/2\). Since \(h=(k_A+k_B)/2\),
\[
h\ge-\tfrac12I-\tfrac34(P_A+P_B). \tag{1}
\]
The overlap is
\[
s=e^{-14/5}\left(1+\tfrac{14}{5}+\tfrac{(14/5)^2}{3}\right),\qquad0<s<1.
\]
The nonzero eigenvectors of \(P_A+P_B\) are proportional to \(\phi_A\pm\phi_B\), with eigenvalues \(1\pm s\). Thus its restriction to **either parity sector has rank one**.

It follows that each parity operator has at most one eigenvalue, counting multiplicity, below \(-1/2\). More precisely, a spectral subspace below that cutoff of dimension at least two would contain a nonzero vector orthogonal to the relevant rank-one direction. Equation (1) gives mean at least \(-1/2\), while spectral support gives a strictly smaller mean. This is a contradiction. Semiboundedness makes this bounded spectral subspace an operator-domain subspace.

A parity trial with mean below \(-1/2\) makes the spectral projection nonzero and therefore rank one. Its eigenvalue \(e_g\) or \(e_u\) is the bottom of the parity spectrum; every other spectral point in that sector is at least \(-1/2\). The index is established before Temple is used.

## Certified Slater moments

Take
\[
f_g=e^{-(6/5)r_A}+e^{-(6/5)r_B},\qquad
f_u=e^{-(3/5)r_A}-e^{-(3/5)r_B}.
\]
These belong to \(H^2\): their second weak derivatives have only bounded exponentially decaying terms and terms \(e^{-ar}/r\), which are locally square integrable. Set
\[
S_p=\|f_p\|^2,\quad K_p=\langle f_p,hf_p\rangle,\quad Q_p=\|hf_p\|^2,\quad
m_p=K_p/S_p,\quad v_p=Q_p/S_p-m_p^2.
\]
The executed interval program proves the following **exact rational** bounds:
\[
-\tfrac54\le m_g\le-\tfrac{1249}{1000},\quad0\le v_g\le\tfrac{23}{500};
\qquad
-\tfrac{117}{200}\le m_u\le-\tfrac{73}{125},\quad0\le v_u\le\tfrac{29}{2000}. \tag{2}
\]

| Trial | Outward mean interval | Outward variance interval | Temple lower endpoint |
|---|---|---|---|
| Even, exponent \(6/5\) | [−1.249784655956, −1.249784655955] | [0.044819988461, 0.045403573585] | −1.310340141087 |
| Odd, exponent \(3/5\) | [−0.584221766334, −0.584221766333] | [0.013735769894, 0.014230463000] | −0.753185961927 |

Both means lie below \(-1/2\), so the preceding rank argument indexes \(e_g,e_u\). Temple in each parity sector gives \(e_p\ge m_p-v_p/(-1/2-m_p)\). Using the lower mean endpoint in the first term and the upper mean endpoint in the positive denominator, (2) implies
\[
e_g\ge-\tfrac54-\tfrac{46}{749}=-\tfrac{3929}{2996}>-\tfrac{33}{25},\qquad
e_u\ge-\tfrac{117}{200}-\tfrac{29}{168}=-\tfrac{1591}{2100}>-\tfrac45. \tag{3}
\]
No observed quadrature convergence is used.

### Integral and arithmetic derivation

The action almost everywhere is
\[
h e^{-ar_A}=\left[-a^2/2+(a-1)/r_A-1/r_B\right]e^{-ar_A}. \tag{4}
\]
There is no delta distribution at the nucleus. Only the strong moment \(\|hf\|^2\), not membership in \(D(h^2)\), is needed.

The complete moment identities and their derivation are also in the human-readable opening docstring of h2/slater_moments.py. Put \(p=aR,t=2p\). Let \(D_X=\pi^{-1}\int e^{-2ar_A}X\), \(O_X=\pi^{-1}\int e^{-a(r_A+r_B)}X\), with subscripts \(A,AA,AB,0\) meaning \(1/r_A,1/r_A^2,1/(r_Ar_B),1\). Then
\[
\begin{aligned}
D_0&=a^{-3},&D_A&=a^{-2},&D_{AA}&=2/a,\\
D_B&=[1/R-e^{-t}(a+1/R)]/a^3,&D_{AB}&=(1-e^{-t})/(Ra^2),\\
D_{BB}&=2R[(1+t)e^{-t}\operatorname{Ei}(t)+(1-t)e^tE_1(t)]/t^2,\\
O_0&=e^{-p}(1+p+p^2/3)/a^3,&O_A&=e^{-p}(1+p)/a^2,&O_{AB}&=2e^{-p}/a,\\
O_{AA}&=\frac{2Re^{-p}}{p^2}[(p+1)(\log(2p)+\gamma)+(1-p)e^{2p}E_1(2p)-p].
\end{aligned} \tag{4a}
\]
For parity sign \(\sigma\), \(k=-a^2/2,d=a-1\), expansion of (4) gives
\[
\begin{aligned}
S/\pi={}&2(D_0+\sigma O_0),\\
K/\pi={}&2[kD_0+dD_A-D_B+\sigma(kO_0+(d-1)O_A)],\\
Q/\pi={}&2[k^2D_0+d^2D_{AA}+D_{BB}+2kdD_A-2kD_B-2dD_{AB}\\
&+\sigma(k^2O_0+(d^2+1)O_{AB}-2dO_{AA}+2k(d-1)O_A)].
\end{aligned} \tag{4b}
\]
Thus both singularities and all cross terms are retained.

For the non-elementary entries, angular integration gives
\[
D_{BB}=2R\int_0^\infty u e^{-tu}\log\frac{u+1}{|u-1|}\,du.
\]
The Laplace transform without \(u\) equals \([e^tE_1(t)+e^{-t}\operatorname{Ei}(t)]/t\), by integration by parts on either side of 1 with cancellation of logarithmic boundary terms. Differentiating yields \(D_{BB}\).

Prolate variables \(\mu=(r_A+r_B)/R,\nu=(r_A-r_B)/R\) have azimuth-integrated volume element \(\pi R^3(\mu^2-\nu^2)/4\). Integration in \(\nu\) gives
\[
O_{AA}=2R\int_1^\infty e^{-p\mu}\left[\mu\log\frac{\mu+1}{\mu-1}-1\right]d\mu.
\]
Writing \(J(p)=\int_1^\infty e^{-p\mu}\log((\mu+1)/(\mu-1))d\mu\), substitution \(\mu=1+u\) and the positive identity \(\log((u+2)/u)=\int_0^2(u+v)^{-1}dv\) allow Tonelli. Integrating successively gives
\[
J(p)=e^{-p}[e^{2p}E_1(2p)+\log(2p)+\gamma]/p.
\]
The derivative identity \((e^xE_1(x))'=e^xE_1(x)-1/x\), with boundary value \(-\gamma\) after adding \(\log x\), verifies the integration. Finally \(O_{AA}=2R[-J'(p)-e^{-p}/p]\).

The code uses
\[
\operatorname{Ei}(x)=\gamma+\log x+\sum_{k\ge1}\frac{x^k}{k\,k!},\qquad
E_1(x)=-\gamma-\log x-\sum_{k\ge1}\frac{(-x)^k}{k\,k!}.
\]
After \(m=100\) terms each absolute tail is bounded by
\[
\frac{x^{m+1}}{(m+1)(m+1)!}\frac1{1-x/(m+2)},\qquad m+2>x>0.
\]
This follows from successive-term ratio \(xk/(k+1)^2\le x/(m+2)\) after the first omitted term. For \(1\le x\le2\), \(z=(x-1)/(x+1)\), the series \(2\sum z^{2j+1}/(2j+1)\) for \(\log x\) has tail at most \(2z^{2m+1}/[(2m+1)(1-z^2)]\). Scaling and inversion reduce all positive rational arguments to this interval. Exponentials use the independently documented outward Taylor/repeated-squaring routine in gaussian/certified_interval.py.

Integral comparison bounds Euler's constant by
\[
H_n-\log n-1/n\le\gamma\le H_n-\log n,\qquad n=32768.
\]
Its equality with the special-function boundary constant follows from
\[
\int_0^n(1-t/n)^n\log t\,dt=\frac{n}{n+1}(\log n-H_{n+1}),
\]
obtained by differentiating the finite beta integral. Dominated convergence gives \(\int_0^\infty e^{-t}\log t\,dt=-\gamma\), and integration by parts gives \(\lim_{x\downarrow0}(E_1(x)+\log x)=-\gamma\). The program uses 256-bit outward dyadic rounding and checks every inequality in (2) as an exact rational comparison.

## Two-electron transfer

**Theorem 1.** The spectral projection of \(H_{\mathcal K}\) onto \((-\infty,-91/50)\) has rank at most one. If a normalized \(\Psi\in D(H_{\mathcal K})\) has mean below \(-91/50\), that projection is rank one, containing its ground eigenvalue \(E\), and
\[
\sigma(H_{\mathcal K})\subset\{E\}\cup[-91/50,\infty). \tag{5}
\]

**Proof.** The simultaneous-inversion-even tensor product is
\[
(\mathfrak h_g\otimes\mathfrak h_g)\oplus(\mathfrak h_u\otimes\mathfrak h_u).
\]
Exchange symmetry restricts each summand to its symmetric tensor square. Let \(p_g\) project onto the unique ground state of \(h_g\), and \(P=p_g\otimes p_g\). Its range in \(\mathcal K\) has dimension one. In the \(gg\) summand outside \(P\), at least one electron lies in the remaining \(g\) spectrum, so \(h_1+h_2\ge e_g-1/2\ge-91/50\); with both outside the bound is \(-1\). The \(uu\) summand has lower bound \(2e_u\ge-8/5>-91/50\). On \(P\), use \(2e_g\ge-66/25\). Nonnegative repulsion gives
\[
H_{\mathcal K}\ge(h_1+h_2)|_{\mathcal K}
\ge-\tfrac{66}{25}P-\tfrac{91}{50}(I-P). \tag{6}
\]
These are form inequalities. The rank-one spectral argument after (1) proves the rank bound; the trial makes the projection nonzero. Its restriction is a single eigenvalue, proving (5). ∎

## Full fermionic ground identification

**Theorem 2.** If the trial in Theorem 1 exists, \(E\) is both the unrestricted scalar spectral bottom and the full spin-fermionic ground energy \(E_0\).

**Proof.** By the \(g\oplus u\) decomposition and (3), \(h\ge-33/25\). HVZ puts the unrestricted scalar essential-spectrum threshold at \(\inf\sigma(h)\ge-33/25\). A trial mean below \(-91/50<-33/25\) therefore makes the scalar bottom a discrete eigenvalue.

The Coulomb semigroup on connected \(\mathbb R^6\) improves positivity. For completeness, Brownian motion with generator \(\Delta/2\) satisfies
\[
\sup_x\mathbb E_x|B_s-C|^{-1}=\sqrt{2/(\pi s)},\qquad
\sup_x\mathbb E_x\int_0^t|B_s-C|^{-1}ds=2\sqrt{2t/\pi}.
\]
The maximum is at \(C\), by radial Gaussian convolution and angular integration. For the relative coordinate of two independent Brownian motions, the generator is \(\Delta\), giving bounds \(1/\sqrt{\pi s}\) and \(2\sqrt{t/\pi}\). Thus all five Coulomb time integrals are finite almost surely. The four attractive nuclear terms sum to at most \(8\sqrt{2t/\pi}\le1/2\) for \(t\le\pi/512\). Khasminskii's geometric-series estimate bounds their exponential moment by 2 on such an interval; the Markov property iterates this for all finite times.

Feynman–Kac expresses the kernel as a strictly positive free Brownian-bridge density times the expectation of a strictly positive potential weight. Conditioning gives finite Coulomb time integrals for almost every pair of endpoints; the exponential estimate handles the negative part. The kernel is therefore positive almost everywhere, so a nonzero nonnegative function has a strictly positive image. The positivity-improving spectral theorem makes an isolated scalar ground eigenvalue simple, with a strictly positive normalized eigenfunction \(\psi_0\).

Exchange and simultaneous inversion commute with \(H_{\rm sc}\) and preserve positivity and norm. Each fixes \(\psi_0\): simplicity gives proportionality and positivity forces the unit-modulus constant to be 1. Hence \(\psi_0\in\mathcal K\), so the scalar bottom is \(E\).

The spin-independent operator acts on four spatial spin components; every normalized fermionic function has energy at least \(E\). Conversely \(\psi_0\) times the antisymmetric two-spin singlet is a normalized fermionic eigenfunction of energy \(E\). Thus \(E_0=E\). ∎

Self-adjointness, HVZ, Feynman–Kac and the positivity-improving spectral theorem are explicit standard paper dependencies, not Lean-checked results. Omitting the positivity/ground-identification argument would leave the symmetry restriction unjustified for the original problem.

## Temple conclusion

For every normalized \(\Psi\in H^2(\mathbb R^6)\) invariant under exchange and simultaneous inversion, if
\[
m=\langle\Psi,H\Psi\rangle<-91/50,\qquad v=\|H\Psi\|^2-m^2,
\]
then the **full fermionic ground energy** obeys
\[
m-\frac{v}{-91/50-m}\le E_0\le m. \tag{7}
\]
The same trial supplies the existence hypothesis. For \(m\in[m_-,m_+]\), \(v\le v_+\), use \(m_- -v_+/(-91/50-m_+)\) as lower endpoint when \(m_+<-91/50\).

For completeness, on a spectrum with only \(E_0<\beta\), the product \((\lambda-E_0)(\lambda-\beta)\) is nonnegative. Integrating against the normalized trial spectral measure gives \(v-(m-E_0)(\beta-m)\ge0\); division by \(\beta-m>0\) is Temple. Only the strong second moment is used.

An accurate H₂ trial at this geometry has denominator about \(0.0688\) Hartree, so variance around \(6.8\times10^{-7}\) gives a \(10^{-5}\)-Hartree correction. Actual certificates use rational endpoints. This fixed-instance separator implies no variable-particle-count or precision cost theorem.

## An unsuitable substitution

A full-fermionic argument using only \(H\ge h_1+h_2\) would need the second noninteracting level above the cutoff. Independent floating-point Gaussian diagnostics gave even/odd trial energies \(a\approx-1.284264306457\), \(b\approx-0.612070124782\), and \(a+b\approx-1.896334431239\). The Slaters \(f\uparrow\wedge f\downarrow\) and \(f\uparrow\wedge g\uparrow\) have orthogonal spin projections and diagonal noninteracting form entries \(2a,a+b\). Certified versions would put its second level below \(-1.896\), obstructing a near-ground cutoff from that comparison alone. Those Gaussian numbers remain **EMPIRICAL**; the certified parity proof above does not depend on them.
