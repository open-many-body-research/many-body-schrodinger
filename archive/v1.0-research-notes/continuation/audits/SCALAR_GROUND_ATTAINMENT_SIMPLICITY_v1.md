> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Scalar ground simplicity from actual bottom attainment

Evidence category: **conditional paper theorem on the actual continuum**.
This result removes the independent scalar-simplicity premise from the
previous two-electron symmetry comparison. Attainment remains an explicit
premise. No existing sealed theorem is changed.

## 1. Scope and strongest exact conclusion

Let \(N\ge1\), \(Z\ge0\). On the scalar Hilbert space
\(L^2(\mathbb R^{3N};\mathbb C)\), use
\[
 H=-\tfrac12\sum_{i=1}^N\Delta_i
       -Z\sum_i|x_i|^{-1}+\sum_{i<j}|x_i-x_j|^{-1},
 \qquad D(H)=H^2(\mathbb R^{3N}).
\]
Assume its actual self-adjoint semibounded realization, and let
\(E=\inf\operatorname{spec}H\in\mathbb R\). Suppose this bottom
is attained by some \(0\ne g\in D(H)\), \(Hg=Eg\).

Then the scalar E-eigenspace has complex dimension one. It has a
unique unit nonnegative representative \(\psi\), and its canonical
locally Lipschitz version is strictly positive at every configuration.
Every simultaneous spatial rotation and every electron-position
permutation fixes this \(\psi\).

For \(N=2\), the scalar and full fermionic spectral bottoms coincide,
and the full fermionic ground eigenspace is exactly
\(\mathbb C(\psi\otimes\chi_{\rm singlet})\). Any independently proved
scalar ground-complement lower bound transfers to the full fermionic
ground complement with its unchanged constant, by the sealed previous
comparison.

There is no assumption of an isolated eigenvalue, a spectral gap, or
a rank-one form bound in the scalar simplicity theorem. Conversely,
this theorem does not prove that the bottom is attained for any input,
nor that all \(N\) electrons bind. It does not identify the scalar and
fermionic bottoms for \(N\ge3\).

## 2. A homogeneous modulus lemma on the actual domain

Write the scalar H1 form as
\[
 q(u,v)=\tfrac12\sum_k\int\overline{\partial_k u}\,\partial_kv
                  +\int V\overline u v,\qquad
 q_E(u,v)=q(u,v)-E\langle u,v\rangle,
\]
with inner products conjugate-linear in the first argument. The
actual self-adjoint spectral lower bound and weak H1 density give
\[
                  q_E(u,u)\ge0\qquad(u\in H^1).                \tag{S1}
\]
Here there is no hidden extension of the form domain. Configuration
Hardy gives a finite constant \(K\) with
\(\|Vu\|_2\le K\|\nabla u\|_2\) on actual H1; for example the
previously proved \(K=2Z\sqrt N+\sqrt{NJ}\), \(J=N(N-1)/2\),
works. It makes the Coulomb form continuous in the H1 norm:
\[
 |\langle Vu,u\rangle-\langle Vv,v\rangle|
 \le K\|\nabla(u-v)\|_2\|u\|_2+
                               K\|\nabla v\|_2\|u-v\|_2 .
\]
Compact smooth H2 functions are dense in actual H1, proving (S1)
from the operator-domain inequality.

For **any** actual ground eigenfunction \(h\in H^2\), not
necessarily normalized or real, set \(u=|h|\). The Sobolev modulus
chain rule gives \(u\in H^1\), \(\|u\|_2=\|h\|_2\), and
\(|\nabla u|\le|\nabla h|\) almost everywhere. Thus
\[
             0\le q_E(u,u)\le q_E(h,h)=0.                     \tag{S2}
\]
For \(v\in H^1\), the real quadratic polynomial
\(q_E(u+tv,u+tv)\) is nonnegative for all real \(t\) and
has zero constant term. Its linear coefficient must vanish.
Using \(iv\) as well proves
\[
                         q_E(u,v)=0\quad(v\in H^1).           \tag{S3}
\]
Therefore \(u\) solves the distributional eigen equation. Since
\(Vu\in L^2\) by Hardy,
\[
                         \Delta u=2(V-E)u\in L^2.
\]
The weak Fourier bridge gives every ordered second derivative in
L2, hence \(u\in H^2\) and \(Hu=Eu\). This proves the homogeneous
modulus lemma
\[
       h\in\ker(H-E)\quad\Longrightarrow\quad
                         |h|\in\ker(H-E)\cap H^2.             \tag{S4}
\]
No simplicity was used. The proof is the general-\(N\), homogeneous
form of the modulus step in SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md.

For completeness the complex modulus chain rule can be obtained
from the smooth Lipschitz maps
\(z\mapsto\sqrt{|z|^2+\varepsilon^2}-\varepsilon\), whose real
differentials have norm at most one. Their compositions converge
to \(|h|\) in L2 by domination by \(|h|\); their weak gradients
are uniformly bounded in L2. Weak compactness and the test-function
identity identify the limiting weak gradient and its norm bound.
Equivalently the usual Lipschitz Sobolev chain rule gives the
pointwise gradient inequality used above. Thus the chain rule
does not require a differentiable absolute value at a zero.

## 3. Strict positivity turns one point into a uniqueness test

Normalize the nonzero attained vector \(g\), and set
\(\psi=|g|/\|g\|_2\). By (S4), \(\psi\) is a nonnegative unit
actual-H2 ground eigenfunction. The sealed strict-positivity
theorem gives
\[
                      \psi(x)>0\qquad(x\in\mathbb R^{3N}).    \tag{S5}
\]

Let \(h\) be any real-valued actual ground eigenfunction and
use its canonical locally Lipschitz representative. Fix a
configuration \(x_0\), for example the simultaneous collision
\(x_0=0\), and define the real constant and actual eigenfunction
\[
              a=\frac{h(x_0)}{\psi(x_0)},\qquad w=h-a\psi .
\]
This is legitimate by (S5), and \(w(x_0)=0\). If \(w\ne0\) in
L2, then (S4) makes \(|w|\) a nonnegative nonzero actual-H2
eigenfunction. Strict positivity makes its canonical representative
positive at \(x_0\). On the other hand \(|w|\) as the absolute
value of the continuous representative of \(w\) is continuous
and agrees almost everywhere with that same H2 function.
Uniqueness of continuous representatives makes its value at
\(x_0\) equal to \(|w(x_0)|=0\), a contradiction. Hence
\[
                h=a\psi
       \quad\hbox{for every real actual ground eigenfunction}. \tag{S6}
\]

Now let \(h\) be complex. Complex conjugation preserves the
actual weak H2 domain and commutes with \(H\), since its
coefficients and eigenvalue are real. This follows by conjugating
the weak derivative and L2 graph identities. Therefore
\[
       h_{\mathrm R}=(h+\overline h)/2,\qquad
       h_{\mathrm I}=(h-\overline h)/(2i)
\]
are real actual ground eigenfunctions, including the possibility
that one or both vanish. By (S6),
\(h_{\mathrm R}=a\psi\), \(h_{\mathrm I}=b\psi\) with \(a,b\in\mathbb R\),
and \(h=(a+ib)\psi\). Since \(\psi\ne0\), this proves complex
dimension one.

Any nonnegative unit ground vector is \(c\psi\). Because
\(\psi>0\), nonnegativity makes \(c\) real and nonnegative;
normalization makes \(c=1\). Thus the nonnegative unit choice
is unique. The point evaluation used in (S6) is a proof device
on canonical continuous representatives, not a bounded
evaluation functional on the ambient L2 space or a claimed
computable reconstruction of the eigenfunction.

## 4. Spatial symmetry and exact two-electron application

Simultaneous rotations and electron-position permutations are real
orthogonal changes of configuration coordinates. They preserve
Lebesgue measure, the actual weak H2 domain, the Laplacian and every
term of the scalar potential. Thus their pullbacks preserve the
scalar ground eigenspace and take a nonnegative unit representative
to another nonnegative unit representative. Uniqueness fixes \(\psi\)
under every such pullback. Equality of the continuous versions
holds at every point, including collisions.

When \(N=2\), all premises of the sealed
SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md are now available from
actual scalar bottom attainment: scalar simplicity has just been
derived. Its sections 5–6 give the precise full simultaneous
spatial/spin fermionic conclusions stated in section 1.
The unit spin factor is
\(\chi_{\uparrow\downarrow}=1/\sqrt2\),
\(\chi_{\downarrow\uparrow}=-1/\sqrt2\),
with equal-spin components zero. The scalar positivity does
not mean that these spin components have the same sign.

The simplicity result itself is valid for arbitrary finite \(N\)
in the **scalar** problem. It is not a many-electron fermionic
nondegeneracy theorem. For example, the fully antisymmetric spin
space built from two spin labels has no nonzero vector when
\(N>2\); multiplying the symmetric scalar ground state by a
spin-only factor therefore does not extend this two-electron
identification to \(N\ge3\). Spin or spatial degeneracies in the
physical fermionic problem retain their own obligations.

## 5. Evidence, exact dependencies and remaining frontier

The mathematical change is elimination of the independent scalar
simplicity hypothesis from the earlier paper comparison. The
actual ground vector, its strict positivity, uniqueness, and
spatial symmetry are derived **conditional on scalar spectral
bottom attainment**. The argument uses no gap. Attainment and
its connection to any explicit physical hydrogenic comparison
must still be supplied independently. This is a classical
positivity argument, not a novelty claim and not a Lean theorem.

| Dependency | SHA-256 |
|---|---|
| COULOMB_NONNEGATIVE_STRICT_POSITIVITY_v1.md | fb57d21629cf77c5c7a4194921b7fc2e1a9c1172f15bc909b0836474e82d3a37 |
| SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md | 605b1a0261a74f00d4181c193ffe8515b6a5ee8f4e41eeefcf6b3c02e59fd841 |
| COULOMB_LOCAL_LIPSCHITZ_v1.md | 4429fa7abefc10fc9c0f2c6f3c8c94bf44b424b8c2208539da10017c700d8a78 |
| ../paper/CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md | ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c |

The scalar operator realization and its spectral lower bound are
explicit actual-continuum premises. Their scope is not inferred
from the full fermionic foundation by a change of notation.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen downstream physical-state target is
rwa_proof/RWA_THEOREM.md, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
New continuation files only; no frozen or sealed successful
source was modified. Independent review is required before
treating this new paper proof as reviewed.

