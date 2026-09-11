> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# The continuum-transfer obstruction and the next tractable target

This follow-up uses the completed Gaussian calculation without rerunning its integrals or repeating its tables. The result is a **sharp obstruction to a specified, gap-limited variational transfer**, not a theorem excluding all continuum hardness reductions. Two qualifications are essential: the omission error needs an upper budget, and an interval enclosing encoded energies is different from a pair of decision thresholds.

## 1. PROVEN (paper): the operator theorem and its minimal scalar core

Let \(H\) be any self-adjoint operator bounded below on a Hilbert space, with closed quadratic form \(q\) and finite spectral infimum \(E=\inf\sigma(H)\). Let \(S\ne\{0\}\) be a finite-dimensional subspace of its **form domain**, and set

\[
a=\min\{q[u]:u\in S,\ \|u\|=1\}.
\]

The minimum exists because the restricted form is continuous on a finite-dimensional space and its unit sphere is compact. The variational principle gives \(E\le a\). No eigenvector at \(E\), operator-domain assumption on \(S\), orthonormal input basis, Coulomb cutoff, or spectral gap is needed. If a nonorthogonal basis represents \(S\), \(a\) means its correctly normalized variational minimum, not an eigenvalue obtained by ignoring its Gram matrix.

The previously requested one-sided omission bound (17) is

\[
E\ge a-\eta. \tag{17}
\]

**Sharp theorem.** For any real \(E,a,\eta\),

\[
(17)\quad\Longleftrightarrow\quad \eta\ge a-E. \tag{1}
\]

Consequently, let \(g=B-A>0\), assume \(a\ge A\), and impose an allowed error \(0\le\eta\le g\). If

\[
A>E+g, \tag{2}
\]

then (17) is false. The condition \(a\le B\) is unnecessary. More generally, a specified budget \(\eta\le\theta g\) is excluded whenever \(a-E>\theta g\); the exact constant is one multiplying the actual discrepancy \(a-E\).

**Complete proof.** Rearranging (17) gives (1). Under (2),

\[
E<A-g\le a-g\le a-\eta,
\]

contradicting (17). Equality \(A=E+g\) would not suffice: \(a=A\) and \(\eta=g\) make (17) an equality. Likewise, dropping the error budget invalidates the assertion: \(\eta=a-E\ge0\) always gives equality. For example, \(E=0,a=A=2,B=3,\eta=2\) satisfies (2) and (17) simultaneously. Thus both the strict mismatch and the specified error budget matter. ∎

**Application to the unrestricted Coulomb model.** For finite \(N,M\), positive finite charges, and fixed point nuclei, take the antisymmetric subspace of
\(L^2(\mathbb R^{3N};\mathbb C^{2^N})\), with simultaneous position-and-spin antisymmetry. The operator is the displayed electronic Hamiltonian of the original problem, with domain \(H^2\) intersected with that subspace and form domain \(H^1\) intersected with it. Coulomb multiplication is infinitesimally Laplacian-bounded by Hardy's inequality and interpolation, so Kato–Rellich gives the required self-adjoint operator; the lower bound is also proved explicitly below. The original [analytic foundations](research/analytic.md) spell out these domain arguments and identify the standard background theorems. Nuclear repulsion is not included in the energy convention here.

Apply the sharp theorem with \(E=E_{\rm cont}\). This proves the requested exclusion for every finite-basis encoding satisfying its stated premises, with no dependence on the Gaussian ansatz used earlier.

**Meaning for a promise reduction.** If \([A,B]\) is an *enclosing band* for \(a\), then \(a\ge A\) is automatic. In the usual local-Hamiltonian decision convention, however, \([A,B]\) is the *forbidden decision gap*: YES means \(a\le A\), NO means \(a\ge B\). It is not an enclosing band. For a NO image, (2) gives

\[
a-E\ge B-E>2(B-A),\qquad E<A. \tag{3}
\]

Thus the same raw thresholds misclassify that continuum image as YES, and an omission certificate with \(\eta\le g\) is impossible. For a YES image one cannot infer \(a\ge A\), so that part of the no-go does not apply without another premise. Nor does the theorem exclude a different encoding, different thresholds with a proved comparison, or a reduction that never uses this finite-space transfer. “Does not transfer” here means the alleged gap-preserving transfer through (17) fails; it is not an unconditional complexity-class separation.

Subtracting the same scalar \(c\) from both operators leaves \(a-E\) unchanged. Dividing both energies, gaps and budgets by the same positive scale preserves the obstruction. Subtracting a scalar only from the compressed matrix changes the proposed comparison and does not lower the actual continuum spectrum relative to that matrix.

## 2. PROVEN (paper): explicit physical energy scales

Put \(Z=\sum_A Z_A\), \(C_N=NZ^2/2\), \(E_N=\inf\sigma(H_N)\), and \(E_0=0\). For all nuclear geometries,

\[
\boxed{-C_N\le E_N\le0.} \tag{4}
\]

**Proof of the lower bound.** For \(f\in H^1(\mathbb R^3)\), a center \(R\), and \(Q>0\), square completion gives

\[
\frac12\|\nabla f\|_2^2-Q\int\frac{|f(r)|^2}{|r-R|}\,dr
+\frac{Q^2}{2}\|f\|_2^2
=\frac12\left\|\nabla f+Q\frac{r-R}{|r-R|}f\right\|_2^2\ge0. \tag{5}
\]

For smooth compactly supported functions, this follows by integration by parts using \(\operatorname{div}((r-R)/|r-R|)=2/|r-R|\). The flux through radius \(\delta\) is \(4\pi\delta^2\to0\), so no point mass is present. Hardy's inequality and density extend the identity to \(H^1\), including complex functions by taking real cross terms. Now use the exact form identity

\[
-\tfrac12\Delta-\sum_A\frac{Z_A}{|r-R_A|}
=\sum_A\frac{Z_A}{Z}\left(-\tfrac12\Delta-\frac{Z}{|r-R_A|}\right).
\]

The weights sum to one; (5) bounds each bracket below by \(-Z^2/2\). Apply this in each electron coordinate and sum, including the finite spin sum. Drop the nonnegative electron repulsion. This gives \(q_N[\psi]\ge-C_N\|\psi\|^2\), also on the antisymmetric subspace, and hence the lower half of (4).

**Proof of the upper bound.** Choose a normalized smooth compactly supported antisymmetric spinor \(\psi\), obtainable from a determinant of disjoint spatial bumps. Dilation by \(L\) preserves its norm and antisymmetry, scales kinetic energy to \(T/L^2\) and electron repulsion to \(W/L\). All nuclear attractions are nonpositive, so \(E_N\le T/L^2+W/L\). Let \(L\to\infty\). ∎

If the specified **ionization margin** is

\[
E_{N-1}-E_N\ge\mu>0,
\]

then \(E_{N-1}\le0\) gives

\[
-C_N\le E_N\le-\mu. \tag{6}
\]

HVZ identifies \(E_{N-1}\) as the bottom of the essential spectrum for this full spin-antisymmetric, fixed-nuclei model; the margin therefore ensures a bound ground eigenvalue. This standard spectral fact is paper background, not part of the Lean formalization. An additional consistency bound is \(\mu\le Z^2/2\): decompose off one electron, use \(H_{N-1}\ge E_{N-1}\) on antisymmetric slices and the one-electron bound above, and drop its repulsions to obtain \(E_N\ge E_{N-1}-Z^2/2\).

For any variational transfer with \(0\le a-E_N\le\eta\), (6) implies the precise necessary condition

\[
\boxed{-C_N\le a\le-\mu+\eta.} \tag{7}
\]

In particular, \(\eta\le\theta g\) requires \(a+\mu\le\theta g\). If \(\theta g<\mu\), the projected minimum must be negative. Without binding, replace \(\mu\) by zero. These are constraints on the energy meant to approximate the physical bottom; trial energies themselves have no upper physical bound.

**Quantifying a nontrivial common promise window.** Consider a family with \(C_N\le C_{\max}\) and ionization margins at least \(\mu_{\min}>0\). Suppose one common pair \(A<B\) has both a physical YES witness \(E_Y\le A\) and a physical NO witness \(E_{\rm No}\ge B\). Then

\[
\boxed{-C_{\max}\le A<B\le-\mu_{\min},\qquad
0<g\le C_{\max}-\mu_{\min}.} \tag{8}
\]

Indeed \(-C_{\max}\le E_Y\le A\) and \(B\le E_{\rm No}\le-\mu_{\min}\); subtract. If \(N\le n^p\), \(M\le n^q\), and \(Z_A\le Z_*\), one may take

\[
C_{\max}(n)=\tfrac12Z_*^2n^{p+2q}. \tag{9}
\]

Thus nontrivial common physical thresholds occupy a polynomial energy band in this bounded-charge family. The coarse bound does not depend on the nuclear coordinate grid. Adding nuclear repulsion requires adding its geometry-dependent scalar to (4)–(7), and does not leave the unshifted common window (8) unchanged.

An arbitrary enclosing interval can be padded without limit, so its width and position do **not** obey (8). Input-dependent threshold pairs likewise need not have both witnesses for each pair. Therefore the unqualified assertion that *any* window of *any* reduction must satisfy (8) would be false; (7) is the instancewise statement, and (8) is the statement for nontrivial common thresholds.

There is a useful explicit scaling consequence. Let a source promise have common thresholds \(u<v\), gap \(\Delta=v-u\), and a common affine encoding \(c+\rho e\), \(\rho>0\). If the finite-space error is at most \(\delta\) and the one-sided continuum error at most \(\eta\), valid continuum thresholds are

\[
A=c+\rho u+\delta,\quad B=c+\rho v-\delta-\eta,
\quad g=\rho\Delta-2\delta-\eta.
\]

The asymmetric \(\eta\) is due to \(E_N\le a\) on the YES side. If both labels have image witnesses and \(2\delta+\eta\le\theta\rho\Delta\) for \(0\le\theta<1\), (8) gives

\[
\boxed{\rho\le\frac{C_{\max}-\mu_{\min}}{(1-\theta)\Delta}.} \tag{10}
\]

Every extra hypothesis in this scaling statement matters, especially the common thresholds and shift. It is a necessary condition, not a sufficient transfer test. Further proofs and counterexamples are in [physical_scales.md](nogo/physical_scales.md).

## 3. PROVEN (Lean): exactly what was checked

Ten new theorems extend [Boundary.lean](formal/Boundary.lean), with all hypotheses exposed. [NOGO_STATEMENTS.md](formal/NOGO_STATEMENTS.md) supplies a complete human proof followed by a plain-English paragraph for **each** theorem. The main formal statement is:

```lean
theorem promise_gap_blocks_lower_bound_transfer (E a A B η : ℝ)
    (_hgap : 0 < B - A) (hretained : A ≤ a)
    (hmismatch : E + (B - A) < A) (hbudget : η ≤ B - A) :
    ¬ (a - η ≤ E) := by
  apply lower_bound_transfer_below_critical E a η
  linarith
```

The other additions establish the exact critical error and its equality/strict cases, an unrestricted-error equality witness, the NO-side discrepancy exceeding twice the gap, the unchanged YES-cutoff consequence, (7) **conditional on its energy premises**, and the gap part of (8) **conditional on both witnesses**. The smallest scalar theorem, `lower_bound_transfer_iff`, has no sign, window or operator hypotheses at all.

The physical derivation of \(C_N\), the definition and analytic properties of the Coulomb operator, and its ionization margin remain **PROVEN (paper)**. These have not been substituted by axioms or advertised as consequences of the scalar Lean proofs. No new algorithm is formalized or claimed. [HubbardDimer.lean](formal/HubbardDimer.lean) is retained unchanged in the aggregate build.

The project pins Lean `v4.34.0-rc2`, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, and Mathlib `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. Reproducible build and audit evidence is in [formal/nogo-logs](formal/nogo-logs/README.md). Historical Gaussian logs refer to their earlier source version and are preserved separately.

The aggregate build completed successfully with exit code 0 (3090 jobs). The standalone axiom audit checked all **54** theorems: 34 in `Boundary.lean` and 20 in `HubbardDimer.lean`. Every dependency list contains only Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`. The final supplementary source audit passed with zero `sorry`, `admit`, custom `axiom`, or `native_decide` tokens outside comments. Exact source hashes, commands and exit codes are retained in the logs; an initial premature supplementary audit is recorded rather than hidden.

## 4. What survives: assessment (3c), neither direction established

A polynomial energy band accommodates an inverse-polynomial promise gap. The bounds therefore do not exclude continuum QMA hardness. Counting separated energy bins also does not help: a decision reduction need not assign distinct energies to distinct input strings. Conversely, energy-scale compatibility supplies no construction or algorithm.

Here is a precise unresolved target, **not a candidate construction**. The source is a rational 2-local Hamiltonian \(K_x\) of polynomial norm with thresholds \(u_x<v_x\), source gap \(v_x-u_x\ge1/q(|x|)\) for a fixed polynomial \(q\), and the promise \(\lambda_{\min}(K_x)\le u_x\) or \(\lambda_{\min}(K_x)\ge v_x\). Seek a uniform polynomial-time map producing \(N_x,M_x\le p(|x|)\), integer \(1\le Z_A\le Z_*\), and distinct nuclei on \(p(|x|)^{-1}\mathbb Z^3\cap[-p(|x|),p(|x|)]^3\), together with polynomial-bit rationals \(\alpha_x>0\), \(\beta_x\in\mathbb Q\), and \(\delta_x\ge0\), where both \(\alpha_x\) and its reciprocal are polynomially bounded, such that

\[
|E_{N_x}-(\alpha_x\lambda_{\min}(K_x)+\beta_x)|\le\delta_x,
\]
\[
\alpha_x(v_x-u_x)-2\delta_x\ge1/p(|x|),\qquad
E_{N_x-1}-E_{N_x}\ge1/p(|x|). \tag{11}
\]

If proved, thresholds \(\alpha_xu_x+\beta_x+\delta_x\) and \(\alpha_xv_x+\beta_x-\delta_x\) would give the desired reduction. This last scalar step is straightforward; (11) is not established here.

The missing **nuclear-Coulomb low-energy simulation lemma** would have to identify the intended occupancy and spin sector, reproduce effective couplings with a total error below the decision gap, lower-bound **all** competing charge arrangements and continuum states, control couplings to that complement, and preserve the ionization margin under polynomial descriptions. Localizing some chosen orbitals proves none of those global lower bounds. Positive nuclei also do not provide independently tunable electric wells, magnetic couplings and electron repulsions. No layout meeting these obligations has been constructed in this work.

For a specified finite-rank projection with range in \(D(H)\), a concrete sufficient bridge remains the earlier lemma: if \(a=\min PHP\), \(b\ge\|QHP\|\), \(q_H[y]\ge d\|y\|^2\) throughout the complementary form domain, and

\[
d\ge a-\eta+b^2/\eta,\qquad\eta>0,
\]

then \(E_N\ge a-\eta\). The scalar square completion is already Lean-checked. The elevated Gaussian instance cannot satisfy its conclusion for the useful error budget. A different low-energy construction would need to prove its own complement estimates; the global constants in (4) alone are too coarse to do so.

In the other direction, excluding every bounded-charge/grid encoding would need a structural theorem covering every such layout, or a polynomial algorithm for the entire promised family together with an appropriate complexity separation assumption. The present bounds do not provide either. This is why the correct choice is (3c), not a speculative construction or a universal no-go. [hardness_status.md](nogo/hardness_status.md) makes the target and missing estimates explicit.

## 5. CONJECTURED: a narrower tractable-class pivot

For the next session I recommend the tractable-class direction, beginning with a fixed two-electron continuum class. This offers a specific approximation-and-certification theorem to attack. The hardness direction currently lacks an actual low-energy nuclear construction and several independent global estimates. This recommendation is a research judgment, not evidence that continuum hardness is false.

The proposed class and theorem, including a constructive form-norm approximation lemma, are specified in [tractable_target.md](nogo/tractable_target.md). The class fixes two electrons, one or two positive nuclei of bounded integer charge, a compact range of internuclear separations bounded away from collision, and positive uniform ionization and simple-ground spectral margins. Inputs are rational geometries; output precision is \(2^{-k}\), and bit cost must include the geometry input length \(L\). The proposed theorem is a classical certified energy algorithm with cost \(C(L+k)^p\), with constants depending only on the fixed class bounds.

This remains a conjecture. A spectral gap controls spectral stability; it does not by itself supply a constructible approximation rate or a continuum lower certificate. The theorem to attempt is uniform constructive approximation in the \(H^1\) form norm by geometrically graded polynomial spaces, with explicit constants, polynomial dimension, and certified integration and linear algebra. Coulomb collision sets, their intersections, and the unbounded exterior all enter that theorem. Ordinary conforming \(H^1\) finite elements need not lie in \(H^2\), so an \(L^2\) operator residual cannot be invoked for them without an additional argument.

There is a concrete **PROVEN (paper), conditional** bridge to the omission bound. For two electrons let \(Z=\sum_AZ_A\), \(K=2Z+1\), and \(B_0=Z^2\). Hardy's inequality gives \(|q[f]|\le K\|f\|_{H^1}^2\), and (4) gives \(|E_2|\le B_0\). Suppose a constructed space \(V_p\) approximates the normalized true ground state in \(H^1\) within \(\varepsilon_p=C_0e^{-cp}\le1/2\), with explicit known \(C_0,c>0\). If \(a_p\) is its exact Ritz minimum, then

\[
\boxed{a_p-4(K+B_0)C_0^2e^{-2cp}\le E_2\le a_p.} \tag{12}
\]

To prove it, choose \(v\in V_p\) with that approximation error, put \(e=v-\psi_0\), and use the weak eigenvalue equation to obtain \(q[v]-E_2\|v\|^2=q[e]-E_2\|e\|^2\). Bound the right side by \((K+B_0)\varepsilon_p^2\), use \(\|v\|\ge1/2\), and minimize the Rayleigh quotient. Thus the requested approximation lemma would supply an effective continuum lower certificate directly. Its effective rate, construction cost and certified matrix computations are the unproved parts; convergence alone does not suffice.

This would be a sufficient tractable subclass of genuine Coulomb molecules. It would neither scale to unbounded electron count nor characterize **exactly all** physically relevant tractable classes as the original tier (c) requested. Arbitrarily stretched limits with closing gaps are outside the stated uniform predicate. No claim is made that this conjecture or approximation strategy is new in the literature; no literature survey was repeated for this follow-up.

## 6. Evidence separation and avoided hand-waves

- **PROVEN (Lean):** ten new scalar implications, including the sharp transfer threshold and conditional physical-window consequences. The aggregate project also retains all earlier theorems.
- **PROVEN (paper):** the operator-level application, the Coulomb bound (4), its margin refinement, and the threshold/affine consequences with the stated hypotheses. Kato–Rellich and HVZ are explicitly identified background results.
- **EMPIRICAL:** no new experiments or numerical claims. The preceding certified Gaussian artifacts are reused only as motivation; their integrals were not rerun.
- **CONJECTURED / unresolved:** the existence or nonexistence of (11), and the proposed polynomial-time certified continuum algorithm for the narrow two-electron class.

The places where an unjustified inference was tempting were: omitting the error budget; treating an enclosing band as a decision gap; assuming both promise labels without witnesses; bounding padded or input-dependent thresholds; treating an affine shift as physical confinement; identifying a finite-space eigenpair with the spectral bottom; confusing ionization, excitation and decision gaps; inferring tractability from a polynomial energy range or a spectral gap; applying an operator residual outside the operator domain; and calling a sufficient tractable subclass an exhaustive classification. Each was replaced by an explicit hypothesis, a counterexample, or a named unproved lemma above.

The remaining theorem to prove or refute is: **For fixed charge, separation, ionization-margin and simple-ground-gap bounds in the two-electron Coulomb class just specified, there is a deterministic classical algorithm which, for every promised rational geometry of bit length \(L\) and every integer \(k\ge1\), returns rational \(\ell\le E_2\le u\) with \(u-\ell\le2^{-k}\) using at most \(C(L+k)^p\) bit operations.**
