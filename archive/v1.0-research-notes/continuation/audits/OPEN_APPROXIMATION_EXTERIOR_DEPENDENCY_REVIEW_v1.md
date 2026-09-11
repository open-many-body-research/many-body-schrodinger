> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exterior dependency review for the OPEN approximation lemma

Date: 2026-09-10. Evidence: focused adversarial paper review, including an explicit nonphysical counterexample. No new Lean proof, source rebuild, numerical certificate, or verdict on the entire OPEN approximation lemma is supplied here. The parent owns the canonical review and its required verdict.

Frozen snapshot: `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. All sources were read without modification. The two frozen analytic-source hashes below were recomputed and matched `FREEZE_MANIFEST.json`.

## 1. Exact conclusion under review

The exterior input G2 concerns the actual reduced physical wavefunction, not its cusp-conjugated remainder. Set

\[
r=|x_1|=b+c,\quad s=|x_2|=a+c,\quad u=|x_1-x_2|=a+b,
\quad S=r+s=a+b+2c.
\]

For every fixed \(d_*>0\), the new paper theorem asserts that an actual real bounded distributional solution of

\[
[-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u-E]\psi=0,
\qquad Z\ge0,
\]

with simultaneous rotation invariance and \(\|\psi\|_\infty\le M_\psi\), has compatible holomorphic perimetric germs at every \(x=(a,b,c)\ge0\), \(S(x)\ge d_*\), on the complex sup polydisc

\[
D\left(x,\frac{H}{1+S(x)}\right),\qquad |\widehat\psi_{\mathbb C}|\le C_\infty M_\psi.
\]

Here \(H>0,C_\infty<\infty\) depend only on \(Z,|E|,d_*\), through the displayed component constants. They are independent of the center and derivative order. Cauchy's estimate is therefore

\[
|\partial^\nu\widehat\psi(x)|\le C_\infty M_\psi\,\nu!
\left(\frac{1+S(x)}H\right)^{|\nu|}.
\]

No ground-state gap, binding, exponential decay, exchange symmetry, or normalization is a hypothesis of this exterior PDE theorem. Such hypotheses enter other parts of the physical or computational composition. Pointwise collision values are the canonical limits supplied by the analytic constructions, not chosen values of an L-infinity representative.

**Focused finding:** no counterexample or unsupported coordinate/parameter passage was found in the reviewed new exterior composition at its stated PDE hypotheses. This is a scoped paper-review finding, not kernel verification or proof of the whole approximation theorem. The inference from finite regularity, real analyticity, symmetry, and exponential H2 decay alone to G2 is false, as Section 4 proves.

## 2. Where uniformity actually comes from

The frozen exterior argument uses fixed small physical charts and the scaled uniform operator lemma. The new exterior argument gives unscaled coefficient formulas and substitutes a direct factorial recurrence with no potential-smallness hypothesis. It does not take a compactness minimum over an unbounded set.

The following dependencies are essential, in this order.

1. **Uniform real amplitude and the actual PDE.** For an eigenfunction this can be supplied by the separate Coulomb boundedness theorem. The new exterior theorem takes the bound as input. Boundedness gives a common L2 norm for the KS pullbacks on fixed seven-dimensional boxes. Merely pulling back a six-dimensional L2 norm would not justify this step near the rank-deficient KS map.
2. **Analytic Coulomb coefficients with separated spectator denominators.** The reciprocal-distance proof uses the polynomial \(\sum_j(x_j+\zeta_j)^2\), not a Hermitian norm as a holomorphic function. For \(|x|\ge d_0\) and \(\|\zeta\|_2\le d_0/8\), its deviation is at most \(17|x|^2/64\). The positive-real branch is bounded by \(2/d_0\), uniformly even when \(|x|\to\infty\).
3. **The actual weak KS lift.** The off-collision chain rule followed by codimension-four L2 removability gives the full weak equation across the selected collision. Removability uses the vanishing local L2 mass against a bounded cutoff-Laplacian L2 norm; it does not assume derivatives or a trace of the input at the collision.
4. **Finite initialization and then a separate all-order theorem.** `GRUSHIN_H12_WEAK_INITIALIZATION_v1.md` supplies H12 from L2, eleven bounded coefficient/source derivatives, and a finite triangular schedule. `GRUSHIN_FACTORIAL_RECURRENCE_v1.md` then supplies factorial bounds from that H12 norm and all-order analytic coefficient bounds. The second result is not a consequence of H12 alone. Its constants contain fixed box margins, the oscillator estimate, coefficient constants, and the H12 amplitude; no derivative-order or distant-spectator parameter is hidden in them.
5. **Quantitative KS descent and rotation invariance.** An invariant analytic lift descends as \(A(X,t)+|X|B(X,t)\), with explicit radii and coefficient bounds linear in the lifted amplitude. The second coefficient has degree \(m-1\) at lifted degree \(2m\). The new descent proof retains that degree and its potentially nonzero constant term. Decomposition uniqueness gives the separate SO(2) invariance needed at axes.
6. **Nonsingular factorial estimates, boundary coordinate control, and gluing.** A separate constant-kinetic elliptic factorial theorem handles the region with all three separations bounded below. SO(2) series handle zero triangle height; the planar square root is used only after a positive height lower bound is proved. Germs agree on full three-dimensional real physical neighborhoods. Convex overlap gluing applies to variable radii, including complex overlap portions outside the physical octant.

The current finite formal results do not themselves replace items 4–6 with an all-order Lean theorem. Their exact finite-gain content remains useful input if the canonical OPEN review retains this route. Conversely, the lack of that formalization is not a mathematical refutation: the referenced paper proofs expressly supply the missing implications.

### Constants checked at the exterior interfaces

With \(d_0=d_*/4\), the new theorem chooses a fixed \(h_0\le1/32\) small enough that all relevant complex spectator displacements are less than \(d_0/8\). Its nuclear coefficient is

\[
B_{\rm nuc}=-8Z+8\varrho[-Z R(t)+R(K(y)-t)]-8E\varrho,
\quad \varrho=\sum_{i=1}^4y_i^2,
\]

with \(c=4\). Its pair coefficient has constant term \(4\), and \(c=1\). The displayed bounds

\[
M_{\rm nuc}=8Z+64h_0^2(Z+1)/d_0+32h_0^2|E|,
\quad M_{\rm pair}=4+64Zh_0^2/d_0+16h_0^2|E|
\]

follow from \(|\varrho|\le4h_0^2\) and the common reciprocal bounds. They are independent of the axis center \(\sigma\ge d_0\).

The H12 instantiation uses outer half-width \(h_0/2\), target half-width \(h_0/4\), and gap \(h_0/136\). The original L2 norm is bounded by \(h_0^{7/2}M_\psi\), so the displayed \(H_jM_\psi\) has no translation factor. The factorial theorem is applied on the inner box with zero source and \(W=1\). Its amplitude is at most \(498H_jM_\psi\). The factor 996 in the holomorphic amplitude is the factor two from the retained complex radius, not an additional solution-dependent constant.

KS descent is used at \(M_y=M_s=r_K^{-1}\), where \(r_K\le1\), so its hypotheses \(M_y,M_s\ge1\) hold. Its half-domain bounds are \(16M_KM_\psi\) and \(16D_KM_KM_\psi\). The chosen axis radius satisfies \(\delta_A D_K\le1/48\), hence the axis bound is less than \(17M_KM_\psi\). In the nonsingular six-dimensional theorem the outer full box width is \(R_C\), giving \(\|\psi\|_2\le R_C^3M_\psi\); the factor 56 is \(2\binom82\). These are consistent with the component domains and norms.

## 3. Escaping clusters and coordinate stress tests

| Configuration family | Required control and review outcome |
|---|---|
| \(x_1\to0\), \(|x_2|\to\infty\) | Fixed nuclear KS charts retain the selected collision. Both other Coulomb denominators stay uniformly separated. The analytic coefficient bound improves with large spectator distance; the common solution amplitude is supplied independently. |
| \(x_1-x_2\to0\), \(|(x_1+x_2)/2|\to\infty\) | Relative/center coordinates give the fixed principal coefficient \(c=1\). Both nuclear denominators stay separated. No assertion that a six-dimensional H2 norm controls the lifted amplitude is used. |
| Two small separations simultaneously | For two electrons this forces the third small by the triangle inequalities and hence forces \(S\) small. Sufficiently thin isolated-pair tubes cannot intersect in \(S\ge d_*\). This does not extend to three electrons or intersecting many-electron strata. |
| Large, nearly collinear triangles with all separations positive | Choosing the shortest separation \(\ell=\min(r,s,u)\) gives \(|\Delta z|\le32\delta\), \(|\Delta\tau|\le6\delta\), and \(|\Delta w|\le2048(1+\ell)\delta\). No ordering is imposed on complex distances; the coordinate choice is made once at each real center. |
| Height tending to zero at infinity | If \(m=\min(a,b,c)<\gamma/(1+\ell)\), a nearby collinear center is covered by its SO(2) invariant series. Otherwise Heron's formula yields \(w_0\ge(2/3)m\ell\ge w_*>0\). Only that latter region divides by \(\sqrt{w_0}\). The conversion therefore costs at most one power of \(1+S\). |
| Overlaps near axes/faces, including nonphysical complex points | Every chart agrees with the physical function on the full real open octant in its domain. The radius-weighted point between real centers lies in both polydiscs and in the closed octant. Its neighborhood contains a real open physical subset, which fixes the entire connected complex overlap. |

The frozen calculation \(|\Delta w|\le102(1+S)\delta\) also has the stated linear loss when its fixed collision-free Cartesian radius and collinear-projection margin are retained. Its pair projected-center lower bound is already corrected to \(D/4\) in the frozen source. No new counterexample to these exterior coordinate estimates was found.

Rescaling a physical germ at \(x=\tau y\), with \(S(y)\le2\), gives radius at least

\[
\frac{H}{\tau(1+2\tau)}\ge\frac{H/2}{(1+\tau)^2}.
\]

Thus the normalized-shell radius loses two powers of outer scale even though the physical radius loses one. This loss is explicitly retained in `ENDPOINT_ONE_THIRD_v3.md`, E11–E15. Finite-order polynomial fitting, H2 tail transfer, coefficient stability, and algorithmic production remain separate obligations; the radius estimate alone proves none of them.

## 4. An exterior counterexample to the general-regularity shortcut

Let \(X=(x_1,x_2)\in\mathbb R^6\), \(q=|X|^2\), and define

\[
\Psi(X)=e^{-q^2}\bigl(2+\sin(e^q)\bigr).
\tag{C1}
\]

This function is strictly positive, exchange symmetric, invariant even under independent rotations, and real analytic everywhere. It has an entire complexification, obtained by replacing \(q\) with \(\sum_j z_j^2\). It may be normalized in L2 without affecting the following conclusion.

Writing \(F(q)=e^{-q^2}(2+\sin(e^q))\), direct differentiation for real \(q\ge0\) gives

\[
|F|\le3e^{-q^2},\quad |F'|\le(1+6q)e^{-q^2+q},\quad
|F''|\le(8+4q+12q^2)e^{-q^2+2q}.
\]

Since \(\partial_j\Psi=2X_jF'\) and
\(\partial_{jk}\Psi=2\delta_{jk}F'+4X_jX_kF''\), every Cartesian derivative through order two is bounded by

\[
(3+44q+16q^2+48q^3)e^{-q^2+2q}.
\]

The gradient is bounded, so \(\Psi\) is globally Lipschitz. Every exponential weighted H2 integral is finite. In particular its physical exterior H2 norm decays at least exponentially in \(S\), since \(S\le\sqrt2|X|\). Near the vertex, \(\widehat\Psi-\Psi(0)=O(S^2)\) and ordinary local analyticity also supplies the weaker G1 weights for any fixed \(0<\sigma<1\).

Nevertheless (C1) fails G2 for every pair of positive finite radius/amplitude constants. Its reduced quadratic form is

\[
q(a,b,c)=(b+c)^2+(a+c)^2.
\]

Given any \(H>0\), choose \(\theta=\min(H/4,1/4)>0\). At the real physical interior center \(x_t=(t,t,t)\), \(t\ge1\), one has \(S=4t\) and \(Q=q(x_t)=8t^2\). Set

\[
c_t=-t+\sqrt{4t^2+i\theta/2},\qquad z_t=(t,t,c_t),
\]

using the positive-real square-root branch. Then

\[
q(z_t)=Q+i\theta,\qquad
|z_t-x_t|_\infty=|c_t-t|
\le\frac{\theta}{8t}\le\frac{H}{32t}
<\frac{H}{1+4t}.
\]

Here the root has real part at least \(2t\), which bounds the denominator in the difference-of-squares identity by \(4t\). The identity \(|\sin(u+iv)|^2=\sin^2u+\sinh^2v\) gives

\[
|\widehat\Psi_{\mathbb C}(z_t)|
\ge e^{-Q^2+\theta^2}
\left[\sinh(e^Q\sin\theta)-2\right]\longrightarrow\infty.
\tag{C2}
\]

Any holomorphic germ agreeing with the real reduced function on its real neighborhood must equal this entire complexification throughout its connected polydisc. Thus no alternative choice of extension avoids (C2). This disproves even a uniform constant-amplitude G2 bound, despite entire real analyticity, positivity, symmetry, and exponential H2 decay.

**The example is not claimed to solve the Coulomb eigenvalue equation.** It invalidates only replacement of the quantitative PDE argument by those general regularity facts. It is not a counterexample to `EXTERIOR_DISTANCE_ANALYTIC_v1.md` or to the physical ground-state approximation claim. A separate agent checked the formula, derivative estimates, and complex displacement; the reviewer checked them again. Agreement is supporting scrutiny, not a formal proof.

## 5. Cusp extraction at infinity must not replace the target

Let \(f_{\rm cusp}=-ZS+u/2\). Multiplication by \(e^{-f_{\rm cusp}}\) introduces on the real physical cone the factor

\[
e^{ZS-u/2},\qquad (Z-1/2)S\le ZS-u/2\le ZS.
\]

On a G2 polydisc its extra complex variation is bounded, but its real-center amplitude can still grow exponentially with \(S\). Exponential H2 decay at some unspecified rate does not prove cancellation of this factor, still less uniform complex cancellation. The subtraction of a multiple of \((x_1\cdot x_2)\log(r^2+s^2)\) supplies no such general cancellation either.

No illicit transfer of that kind occurs in the examined new endpoint interface: it fits \(\widehat\psi-\psi(0)\), whose G2 amplitude is at most the wavefunction bound plus \(|\psi(0)|\). The actual-eigenfunction composition restricts its extracted-remainder estimate to a small neighborhood of the vertex. The extracted Fock coefficient is not an exterior input. The full review must keep this distinction when comparing other frozen trial classes or extraction arguments.

## 6. Reduced dependency and access boundary

For this exterior route the mathematical inputs to retain are the actual weak Coulomb equation, a uniform real amplitude bound, rotation invariance, the weak KS identity/removability, quantitative finite initialization, both factorial operator estimates, quantitative KS descent, and full-dimensional boundary compatibility. Local Lipschitz regularity is useful elsewhere but is not an additional exterior input once boundedness and the weak equation are supplied. Exponential decay belongs to G3 and is not used to establish G2. The precise Fock coefficient, uniqueness of a ground vector, and a discrete spectral gap are not used by G2.

This review read the local primary project arguments and the stated component proofs below. The new recurrence, descent, coefficient, and gluing arguments are explicit local proofs, so no inaccessible external theorem was substituted for them. The frozen Grušin PDF was located at `rwa_proof/sources/grushin1971.pdf`; it was not reopened or re-audited for this bounded review, and no fresh verification of its printed theorem is claimed. The new direct recurrence avoids reliance on the frozen qualitative-uniformity shortcut. The old H12 note records a failed Hörmander PDF retrieval, but that theorem is expressly not a dependency of its final partial-convolution proof. No web retrieval, compilation, or computation beyond source reading and hashing was needed here.

The next action for the canonical OPEN review is to combine this scoped finding with the vertex/Fock, exact-dictionary, and constructive-coefficient audits. If that review retains the endpoint route, exterior G2 should continue to be consumed as the stated PDE-derived paper theorem until its exact all-order chain is formalized. Neither the counterexample above nor the formalization frontier alone decides the full approximation verdict.

## 7. Source hashes and exact reading scope

Paths beginning `F/` are relative to the frozen snapshot named above. Paths beginning `A/` are relative to `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/`.

| Source | SHA-256 | Reading scope |
|---|---|---|
| F/rwa_proof/EXTERIOR_ANALYTIC_ATTEMPT.md | `6b56710d1a0ad8d4a2bcc20021b69412c1f073961f33243b3378ff50d0c731f5` | Full text, E1–E12 and physical coordinate/exterior claims |
| F/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` | Full text, U1–U12 and composition boundary |
| A/EXTERIOR_DISTANCE_ANALYTIC_v1.md | `e6fdf92081e37aadd515d7badc65bf632ccfead811b388fc148d169b31183360` | Full text; exact exterior theorem and every constant/domain interface |
| A/DISTANCE_BOUNDARY_GERMS_v1.md | `b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991` | Full text; invariant series, axes, collinear/interior maps, gluing |
| A/COULOMB_COMPLEX_COEFFICIENT_BOUNDS_v1.md | `a6b9361f229a29e3df2cf0e3e20552da7cfeb49dfbbf7f8f15d0112375eaa5b5` | Full text; reciprocal branch and actual coefficient formulas |
| A/GRUSHIN_H12_WEAK_INITIALIZATION_v1.md | `ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812` | Full text; quantitative hypotheses, weak initialization and finite schedule |
| A/GRUSHIN_FACTORIAL_RECURRENCE_v1.md | `5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594` | Full text; exact norm, recurrence, initialization and amplitude dependence |
| A/NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md | `d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0` | Full text; actual weak-input factorial estimate and constants |
| A/KS_QUANTITATIVE_DESCENT_v1.md | `17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f` | Full text; degrees, convergence, radii, uniqueness, finite-procedure scope |
| A/KS_WEAK_REMOVABILITY_v1.md | `ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde` | Full text; weak pullback and codimension-four removal |
| A/ENDPOINT_ONE_THIRD_v3.md | `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a` | Sections 1 and 6 read; headings and targeted G2/exterior references inspected elsewhere; no full polynomial-approximation audit |
| A/ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md | `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696` | Full text; distinction between physical G2, local extracted remainder and endpoint inputs |
| F/CORRECTION_PROTOCOL.md | `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3` | Full preservation/correction instructions |
| F/FREEZE_MANIFEST.json | `c01b4f3568b623795c5785282d94c734339445125a990cef054cb1706b3801b0` | Exact entries for the two frozen analytic sources checked against recomputed bytes |

No frozen claim is marked false merely because of the nonphysical counterexample. This new supporting note does not revise any sealed proof, audit, status, or original theorem in place.
