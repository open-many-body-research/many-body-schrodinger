> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Scalar ground symmetry and the exact two-electron fermionic comparison

Evidence category: **conditional paper theorem for actual continuum
operators**. The premise is actual simple scalar spectral-bottom
attainment. This proof derives a nonnegative real representative,
spatial symmetries, equality with the full fermionic ground energy,
and the correct fermionic complement bound. It does not prove
scalar attainment or strict pointwise positivity.

## 1. Actual assumptions and conclusions

Use the scalar Coulomb operator
\[
 H=-\tfrac12(\Delta_1+\Delta_2)-Z/|x_1|-Z/|x_2|+1/|x_1-x_2|,
 \quad D(H)=H^2(\mathbb R^6),\quad Z\ge0,
\]
with its actual self-adjoint semibounded realization and weak H1 form
\[
 q(u,v)=\tfrac12\sum_k\int\overline{\partial_ku}\partial_kv
                                        +\int V\overline u v.
\]
The form is conjugate-linear in the first argument. Suppose
\(E=\inf\operatorname{spec}H\) is finite and is attained by a unit
\(g\in H2\), \(Hg=Eg\), whose E-eigenspace is one-dimensional over
\(\mathbb C\).

Then there is a unique unit nonnegative scalar ground eigenfunction
\(\psi\), with the canonical bounded locally Lipschitz representative,
and
\[
 \psi(Ux_1,Ux_2)=\psi(x_1,x_2)\quad(U\in SO(3)),\qquad
 \psi(x_2,x_1)=\psi(x_1,x_2).                                  \tag{F1}
\]
Let the unit antisymmetric spin vector be
\[
 \chi_{\uparrow\downarrow}=1/\sqrt2,\quad
 \chi_{\downarrow\uparrow}=-1/\sqrt2,\quad
 \chi_{\uparrow\uparrow}=\chi_{\downarrow\downarrow}=0.
\]
The vector \(\Psi_\sigma(x)=\psi(x)\chi_\sigma\) is the unit ground
vector of the full fermionic Hamiltonian, up to complex phase. Its
energy is exactly E and its E-eigenspace is \(\mathbb C\Psi\).
The fermionic space uses simultaneous spatial and spin permutation:
\[
 \Phi_{\tau\sigma}(x_2,x_1)=-\Phi_\sigma(x_1,x_2),                \tag{F2}
\]
where \(\tau\) swaps the two spin labels.

If an actual scalar complement bound is also established,
\[
 \beta\|w\|_2^2\le\langle Hw,w\rangle
 \quad(w\in H2,\ \langle\psi,w\rangle=0),                        \tag{F3}
\]
then every actual fermionic-domain \(\Phi\perp\Psi\) satisfies
\[
 \beta\|\Phi\|_2^2\le
                           \langle H_{\rm ferm}\Phi,\Phi\rangle. \tag{F4}
\]
No ionization threshold is inserted in place of (F3).

## 2. Actual spectral lower bound on the full H1 form domain

The actual self-adjoint spectral lower bound gives
\(q(u,u)\ge E\|u\|_2^2\) for \(u\in H2\).
Configuration Hardy gives a finite constant K such that
\(\|Vu\|_2\le K\|\nabla u\|_2\) for actual H1 functions. Therefore
\[
 |\langle Vu,u\rangle-\langle Vv,v\rangle|
 \le K\|\nabla(u-v)\|_2\|u\|_2
                           +K\|\nabla v\|_2\|u-v\|_2.
\]
Together with kinetic-term continuity and H1 approximation by compact
smooth functions in H2, this gives
\[
 q_E(u,u):=q(u,u)-E\|u\|_2^2\ge0\qquad(u\in H1).                \tag{F5}
\]
The spectrum-to-variational direction uses the actual self-adjoint
operator; a variational definition has not replaced the physical
spectral bottom.

## 3. Modulus minimization returns to the actual operator domain

Set \(u=|g|\). The complex Sobolev modulus inequality gives
\(u\in H1\), \(\|u\|_2=1\), and \(|\nabla u|\le|\nabla g|\)
almost everywhere. The potential terms agree, so
\(q(u,u)\le q(g,g)=E\). By (F5), equality holds.

For every \(v\in H1\), nonnegativity of
\(q_E(u+tv,u+tv)\) for all real t forces
\(\operatorname{Re}q_E(u,v)=0\): otherwise a sufficiently small t
of the opposite sign makes that quadratic polynomial negative.
Replacing v by iv forces its imaginary part to vanish. Thus
\[
 q(u,v)=E\langle u,v\rangle\qquad(v\in H1).                     \tag{F6}
\]
In particular u solves the actual distributional Coulomb equation.
Hardy on u∈H1 gives Vu∈L2, hence
\[
 \Delta u=2(V-E)u\in L2.
\]
The weak Fourier-domain bridge supplies every ordered second
derivative in L2; thus u∈H2. On the actual operator domain,
(F6) is \(Hu=Eu\). No form minimizer has been declared an operator
eigenvector without proving its domain membership.

Take \(\psi=u\) and its continuous representative from the
all-N Lipschitz theorem. It is nonnegative everywhere, because
a negative continuous value would contradict almost-everywhere
nonnegativity on a positive-measure neighborhood. It is real,
unit and nonzero. Simplicity and a nonnegative inner product
show uniqueness among unit nonnegative ground eigenfunctions.

## 4. Every spatial symmetry fixes the nonnegative generator

Simultaneous rotation is unitary on the actual L2 space, preserves
the actual H2 domain, and commutes with H. This follows directly
from the real orthogonal coordinate change: the Laplacian, all
three distances and Lebesgue measure are invariant. Weak derivatives
transform by the same constant matrix. Electron-position exchange
has the same properties.

Let T be one of these pullbacks. The unit ground eigenfunction
Tψ is \(c\psi\) by simplicity, with |c|=1. Both functions are
nonnegative, and
\[
 c=\langle\psi,T\psi\rangle=\int\psi(x)(T\psi)(x)\,dx
                                                    \in[0,\infty).
\]
Therefore c=1, proving (F1). The continuous representatives agree
everywhere. No representation theorem about rotation-group
characters or positivity-improving semigroup is needed.

## 5. Full fermionic spectral bottom and exact ground eigenspace

The full spin operator acts componentwise, on four actual H2
components. Exchange symmetry of ψ and antisymmetry of χ give
(F2) for Ψ. Its norm is one and \(H_{\rm ferm}\Psi=E\Psi\).

For every full-spin domain vector,
\[
 \langle H_{\rm spin}\Phi,\Phi\rangle
 =\sum_\sigma\langle H\Phi_\sigma,\Phi_\sigma\rangle
 \ge E\sum_\sigma\|\Phi_\sigma\|_2^2.
\]
In particular this holds in the fermionic subspace. Its actual
self-adjoint realization and the variational/spectral bridge
therefore have bottom at least E; the actual eigenvector Ψ
gives the opposite inequality.

If Φ is any fermionic E-eigenvector, every component is an actual
scalar E-eigenfunction, so \(\Phi_\sigma=c_\sigma\psi\).
Equation (F2) and symmetry of ψ give \(c_{\tau\sigma}=-c_\sigma\).
This is an L2 identity using the nonzero vector ψ, not division
by its value at an individual point. The equal-spin coefficients
vanish and the remaining two are opposites. Thus \(c\in\mathbb C\chi\)
and \(\Phi\in\mathbb C\Psi\). The ground dimension in the full
fermionic model is exactly one.

## 6. Complement transfer includes every spatial symmetry component

For an arbitrary actual fermionic-domain Φ, set
\(a_\sigma=\langle\psi,\Phi_\sigma\rangle\).
Spatial exchange of the integration variable gives
\[
 a_{\tau\sigma}
 =\int\psi(x_2,x_1)\Phi_{\tau\sigma}(x_2,x_1)\,dx
 =-a_\sigma.
\]
Hence \(a=c\chi\), even when Φ is not an eigenvector.
The full Hilbert inner product is
\[
 \langle\Psi,\Phi\rangle
      =\sum_\sigma\overline{\chi_\sigma}a_\sigma=c.
\]
If Φ⊥Ψ then every scalar projection \(a_\sigma=0\).
Every component therefore satisfies (F3). Summing its four
inequalities proves (F4) with the same β.

There is no factor of two or four from the spin sum. Spatially
antisymmetric components were not omitted; their scalar ground
projection vanishes and they are included in the complement
estimate. This is precisely the physical-domain separator needed
by a rank-one Temple implication.

## 7. Exact dependencies and remaining physical frontier

Actual simple scalar spectral-bottom attainment is an explicit
premise, to be supplied by the separate hydrogenic comparison
and spectral arguments. If these also establish the scalar
complement threshold, Section 6 transfers it without a new
spectral assumption.

The theorem proves nonnegativity and the symmetries used in the
analytic/approximation chain. Strict positivity at every point,
including a nonzero collision value, is not proved here.
The approximation theorem does not require strict positivity.
No corresponding three-electron uniqueness assertion is made.

New paper dependencies:

| Artifact | SHA-256 |
|---|---|
| ../paper/CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md | ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c |
| COULOMB_GLOBAL_BOUNDEDNESS_v1.md | d103aa471fcb626ca330d02a4cfbc6534a038e8827e129cff6c24ef3351377a7 |
| COULOMB_LOCAL_LIPSCHITZ_v1.md | 4429fa7abefc10fc9c0f2c6f3c8c94bf44b424b8c2208539da10017c700d8a78 |

The actual scalar and fermionic self-adjoint realizations and
variational/spectral identification are declared continuum operator
premises here, with separate formal audits. The physical Hamiltonian,
weak H2 domain and simultaneous spin-space permutation are explicit.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen target is the physical ground-state and singlet
interpretation in rwa_proof/RWA_THEOREM.md section 1, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
This proof requires separate independent review. It is not a
Lean theorem or novelty claim. Frozen and sealed successful
artifacts were preserved.

