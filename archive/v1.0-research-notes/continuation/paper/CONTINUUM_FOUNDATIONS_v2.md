> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Continuum Coulomb foundations on the actual weak Sobolev domain

Date: 2026-09-09. Evidence category: **paper proof with explicit classical foundations; not a Lean verification**. This supplies a detailed proof blueprint for F02–F04, not a change to their formal completion status. Its operator is the physical continuum operator, not a finite matrix. No binding, eigenvector, simplicity, spectral gap, approximation rate, algorithm, complexity estimate, or novelty claim follows merely from this file.

The frozen references are `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md`, SHA-256 `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, and `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Neither was modified.

The direct formalization target is `AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean`, SHA-256 `4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e`, under the same post-freeze parent directory. Its `HasH1`, `HasH2`, `targetDomain`, `scalarHamiltonianGraph`, and `hamiltonianGraph` definitions were read. The continuation specification has SHA-256 `901dc028f80c2519ca0985d2a0f7ebf8ec58065b52e37ff3fe224ec1f61e73da`.

Earlier paper reports already give condensed Hardy/Kato and square-completion arguments, particularly `AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`, §1. The contributions here are the expanded weak-domain and form-domain bridges, explicit direct resolvent construction, full simultaneous spin permutation treatment, and a sharper aggregate pair constant. These are standard deductions, with novelty undetermined.

## 1. Exact statement and foundations used

Let N be a finite nonnegative integer and Z a real number. Physical atoms in the specified computable input class have Z≥1; allowing other real Z in this mathematical theorem is not an algorithmic claim for an uncomputable real input. Put d=3N, Σ_N={1,2}^N and

\[
\mathscr H_N=\bigoplus_{\sigma\in\Sigma_N}L^2(\mathbb R^{3N};\mathbb C),
\qquad
\|\psi\|^2=\sum_\sigma\int|\psi_\sigma(x)|^2\,dx.
\]

The sum is a finite Hilbert direct sum, using counting measure in spin. Let P_πx have coordinates (P_πx)_i=x_{π(i)}, and define

\[
(U_\pi\psi)_\sigma(x)=\psi_{\sigma\circ\pi}(P_\pi x),\qquad
\mathscr F_N=\{\psi:U_\pi\psi=\operatorname{sgn}(\pi)\psi\text{ for every }\pi\}.
\]

This is exactly the simultaneous spatial and spin action used by the existing Lean definitions. Define weak H^k componentwise for k=1,2; all spatial partials up to order k must be L² distributions. Write

\[
G(\psi)^2=\sum_{\sigma,i,\alpha}\|\partial_{i,\alpha}\psi_\sigma\|_2^2,
\quad A=-\tfrac12\Delta,\quad D(A)=H^2(\mathbb R^{3N};\mathbb C^{2^N}).
\]

For collision-free configurations set

\[
V_{N,Z}(x)=-Z\sum_i\frac1{|x_i|}+\sum_{i<j}\frac1{|x_i-x_j|}.
\tag{1.1}
\]

The pair term is **repulsive**. Give each inverse distance the value zero on its own zero set, as in Lean's inverse-at-zero convention. Section 2 proves that any finite measurable alternative on those sets produces the same multiplication operator. Let M=\(\binom N2\) and

\[
C_{N,Z}=2|Z|\sqrt N+\sqrt{NM},\qquad Z_+=\max(Z,0).
\tag{1.2}
\]

**Theorem CF.** For every such N and Z:

1. The collision set is Lebesgue null. Multiplication by V maps weak H¹ continuously into L² and obeys \(\|V\psi\|\le C_{N,Z}G(\psi)\).
2. For every ε>0 and every weak H² vector,
   \[
   \|V\psi\|\le\varepsilon\|A\psi\|+
   \frac{C_{N,Z}^2}{2\varepsilon}\|\psi\|.
   \tag{1.3}
   \]
3. The actual weak graph defines one and only one output Hψ for every ψ∈H²∩\(\mathscr F_N\), and no other inputs. This operator is densely defined and self-adjoint on precisely that domain.
4. Its closed form has domain H¹∩\(\mathscr F_N\), with
   \[
   q[\psi]=\tfrac12G(\psi)^2+\sum_\sigma\int V(x)|\psi_\sigma(x)|^2\,dx.
   \tag{1.4}
   \]
   If E=inf σ(H), then
   \[
   -\tfrac12 NZ_+^2\le E\le0,\qquad
   E=\inf_{\substack{\psi\in D(H)\\\|\psi\|=1}}\langle\psi,H\psi\rangle
    =\inf_{\substack{\psi\in H^1\cap\mathscr F_N\\\|\psi\|=1}}q[\psi].
   \tag{1.5}
   \]
   Inner products in (1.5) are real by symmetry. Thus the existing extended-real graph variational infimum equals this finite real spectral infimum.

For N=0, configuration space is a singleton with zero-dimensional Lebesgue mass one, the spin set is a singleton, \(\mathscr H_0=\mathscr F_0=\mathbb C\), all derivatives and Coulomb sums are empty, H=0 and E=0. The proof below treats N≥1, with pair arguments only when N≥2.

The classical foundations used are Lebesgue integration (Tonelli, dominated convergence and change of variables), Hilbert-space completeness and Cauchy–Schwarz, smooth mollification, Plancherel/Fourier inversion with the distributional differentiation rule, and the spectral theorem for self-adjoint operators. Sections 2–10 prove the needed Coulomb deductions. They do not reprove these general foundations or assert that they have all been bridged to the project's Lean types. Section 11 records source checks and their limits. Self-adjointness is proved directly below, rather than made a premise called “Kato–Rellich.”

## 2. Collision nullity and measurable representatives

For each i, the set \(\{x:x_i=0\}\) is a product of a zero-measure singleton in R³ with R^(3N−3). Tonelli applied to its indicator gives measure zero, including on the unbounded product (there is no multiplication of an undefined expression “0 times infinity”). For a pair i<j use the orthogonal coordinates

\[
y=(x_i-x_j)/\sqrt2,\qquad t=(x_i+x_j)/\sqrt2,
\tag{2.1}
\]

with other coordinates unchanged. The collision is {y=0}; the same argument and orthogonal invariance of Lebesgue measure give measure zero. A finite union covers every nuclear or pair collision. Every intersection, including simultaneous nucleus-pair collisions and multiple collision strata, is a subset of this null union.

Distances are continuous and their reciprocals with zero assigned at zero are measurable and finite. Thus V is a real measurable function; modifying it on the collision union does not change products as L² equivalence classes, whenever the products are L². Similarly, modifying the representative of ψ does not change Vψ almost everywhere. This proves representative independence, not a pointwise smoothness assertion at collisions.

## 3. Weak Sobolev density and Fourier bridges

For completeness, the particular approximation and weak-domain facts needed below are as follows. If f has weak derivatives through order k≤2 in L², choose χ∈C_c^∞ with χ=1 on the unit ball and put χ_R(x)=χ(x/R). Distributional Leibniz gives

\[
D^\alpha(\chi_Rf)=\sum_{\beta\le\alpha}
 {\alpha\choose\beta}(D^\beta\chi_R)D^{\alpha-\beta}f.
\]

The β=0 term converges to D^αf in L² by dominated convergence; each other term has norm at most a constant times R^(−|β|) times an L² norm of a lower derivative, hence tends to zero. Convolve χ_Rf with a compact smooth approximate identity. Weak derivatives commute with convolution, and translation continuity in L² gives convergence of each derivative. A diagonal sequence is in C_c^∞ and converges in weak H^k. The same construction works componentwise in the finite spin sum. For k=0 it supplies L² density.

Use the unitary Fourier convention with kernel exp(−ix·ξ). The distributional differentiation rule, proved first by integration by parts on Schwartz tests, gives

\[
\widehat{D_af}=i\xi_a\widehat f,\qquad
\widehat{D_bD_af}=-\xi_a\xi_b\widehat f.
\tag{3.1}
\]

The use of real compact smooth tests in the Lean definition is equivalent to the usual complex distribution tests: split a complex test into real and imaginary parts; L² functions are locally integrable. Compact tests extend to Schwartz tests by cutoffs and Cauchy–Schwarz. Conversely, an L² Fourier multiplier representing a derivative satisfies the compact-test identity by Plancherel. Hence the finite weak-derivative witness in `HasH2` is equivalent to

\[
f\in L^2,\quad |\xi|^2\widehat f\in L^2.
\tag{3.2}
\]

Indeed, existence of all weak second partials gives (3.2) by summing the diagonal ones. Conversely, \(|\xi_a\xi_b|\le|\xi|^2\) controls every mixed second partial, and \(|\xi_a|\le1+|\xi|^2\) controls each first partial. These multipliers and (3.1) provide exactly the witnesses required by `HasH2`, rather than just a formal Laplacian notation.

Plancherel also gives, for all H² spin vectors,

\[
G(\psi)^2\le\|\psi\|\,\|\Delta\psi\|,
\qquad
\sum_{a,b,\sigma}\|D_bD_a\psi_\sigma\|_2^2=\|\Delta\psi\|^2.
\tag{3.3}
\]

For the first identity use Cauchy–Schwarz on the measure space consisting of ξ and the finite spin index; this avoids an unwanted spin multiplicity factor. The second follows from \(\sum_{a,b}\xi_a^2\xi_b^2=|\xi|^4\). In particular the explicit norm

\[
\|\psi\|_{H^2,*}^2=\|\psi\|^2+G(\psi)^2+
 \sum_{a,b,\sigma}\|D_bD_a\psi_\sigma\|_2^2
\]

is equivalent to \(\|\psi\|+\|\Delta\psi\|\). This norm is equivalent to the convention that counts each unordered mixed multi-index once.

## 4. Three-dimensional Hardy, with the origin included

Let f∈C_c^∞(R³;C). On R³\{0} set X=x/|x|²; div X=1/|x|². Integrate div(X|f|²) on an annulus ε<|x|<R containing the support. The outer boundary vanishes. The magnitude of the inner boundary term is at most

\[
\varepsilon^{-1}\int_{|x|=\varepsilon}|f|^2\,dS
\le4\pi\varepsilon\|f\|_\infty^2\longrightarrow0.
\]

All other terms are integrable near zero: |x|^(−2) is locally integrable in dimension three and f,∇f are bounded. Letting ε decrease to zero gives

\[
\int\frac{|f|^2}{|x|^2}
=-2\operatorname{Re}\int\overline f\,\frac{x}{|x|^2}\cdot\nabla f
\le2\left\|\frac f{|x|}\right\|_2\|\nabla f\|_2.
\]

If the first norm vanishes the conclusion is immediate; otherwise divide by it:

\[
\boxed{\left\|f/|x|\right\|_2\le2\|\nabla f\|_2.}
\tag{4.1}
\]

Now approximate any weak H¹ f by compact smooth f_m in H¹, as in §3. Applying (4.1) to differences shows f_m/|x| is L²-Cauchy. Let its limit be g. Choose a common subsequence converging almost everywhere both for f_m→f and f_m/|x|→g. Off the null origin, g=f/|x|. Thus multiplication is the actual inverse-distance product and the norm inequality passes to the limit. No zero trace at the origin, pointwise value, or vanishing near the origin was assumed.

## 5. Slicing, spin summation, and the checked constants

First take a compact smooth configuration-space spin vector. Fix all coordinates except x_i and apply (4.1) to the three-dimensional slice, then integrate its squared inequality in spectator variables and sum the spin components. Tonelli applies to the nonnegative integrands. Approximation in H¹ and the same Cauchy/a.e.-identification argument as in §4 give, for every weak H¹ vector,

\[
\|\psi/|x_i|\|\le2\|\nabla_i\psi\|.
\tag{5.1}
\]

Here the norm on each gradient includes all spin components and all three physical gradient components. This proof does not assume in advance that arbitrary weak H¹ slices have already been identified in a separate slicing theorem; it constructs the required configuration-space multiplier directly. Such a slicing theorem is an alternative route, not an additional unproved premise of (5.1).

For i<j, the orthogonal transformation (2.1) preserves every relevant L² norm and weak H¹; the latter follows by the distributional chain rule, or by smooth approximation. Since |x_i−x_j|=√2|y| and

\[
\nabla_y=\frac{\nabla_i-\nabla_j}{\sqrt2},
\]

Hardy in y yields the stronger pair estimate

\[
\boxed{\|\psi/|x_i-x_j|\|\le\|(\nabla_i-\nabla_j)\psi\|.}
\tag{5.2}
\]

In particular its square is at most \(2(\|\nabla_i\psi\|^2+\|\nabla_j\psi\|^2)\). This recovers the earlier paper bound.

All \(g_i=\nabla_i\psi\) belong to the *same* Hilbert space of three-component vector fields over the full configuration/spin measure. The identity

\[
\sum_{i<j}\|g_i-g_j\|^2
 =N\sum_i\|g_i\|^2-\left\|\sum_i g_i\right\|^2
 \le N G(\psi)^2
\tag{5.3}
\]

follows by expanding all inner products and taking real parts. Triangle and finite Cauchy–Schwarz now give

\[
\begin{aligned}
\|V\psi\|
&\le2|Z|\sum_i\|g_i\|+\sum_{i<j}\|g_i-g_j\|\\
&\le\left(2|Z|\sqrt N+\sqrt{NM}\right)G(\psi).
\end{aligned}
\tag{5.4}
\]

For N≥2, \(\sqrt{NM}\le(N-1)\sqrt N\), because N/2≤N−1. For N=1 the pair sum is zero. Thus the continuation specification's estimate

\[
\|V\psi\|\le\sqrt N(2Z+N-1)G(\psi)
\tag{5.5}
\]

is correct on its physical range Z≥0. Its use for unrestricted signed Z would require |Z|. The aggregate pair part in (5.4) is strictly smaller for N>2; no optimality is claimed. Every constant is independent of spin multiplicity because spin was summed in a Hilbert norm before Cauchy–Schwarz.

## 6. Infinitesimal relative bounds and actual weak graph existence

Combine (3.3) and (5.4). Since \(\|\Delta\psi\|=2\|A\psi\|\),

\[
\|V\psi\|\le C_{N,Z}\sqrt{2\|A\psi\|\|\psi\|}
\le\varepsilon\|A\psi\|+
 \frac{C_{N,Z}^2}{2\varepsilon}\|\psi\|.
\]

The last inequality is the nonnegative square of
\(\sqrt{\varepsilon\|A\psi\|}-C_{N,Z}\sqrt{\|\psi\|/(2\varepsilon)}\).
Equivalently the coefficient of \(\|\Delta\psi\|\) may be chosen δ>0 with remainder \(C_{N,Z}^2/(4\delta)\|\psi\|\). These are operator bounds, not only form bounds.

For each weak H² spin component choose its L² first and mixed second derivatives. Finite choice assembles them into the exact d and e witnesses in `scalarHamiltonianGraph`. By (5.4), Vψ∈L², so

\[
h=-\tfrac12\sum_aD_aD_a\psi+V\psi
\tag{6.1}
\]

is an actual L² vector and satisfies the graph's almost-everywhere equation. Weak derivative uniqueness makes it independent of the choices. Conversely the graph explicitly supplies every first and second weak partial, so its input belongs to weak H². §7 proves h is fermionic whenever ψ is; existing graph uniqueness then identifies (6.1) with the sole output of the exact graph. This does not replace a constructive numerical algorithm by a choice: it constructs a mathematical unbounded operator from derivatives already uniquely specified in L². No executable approximation procedure is claimed.

## 7. Fermionic symmetry, dense domain, and cores

Each P_π is orthogonal in R^(3N), and σ↦σ∘π is a permutation of the finite spin set. Hence U_π is unitary. Its inverse is U_(π⁻¹); the composition law under the chosen convention is U_πU_τ=U_(π∘τ). The finite antisymmetrizer

\[
\mathcal P_- =\frac1{N!}\sum_{\pi\in S_N}\operatorname{sgn}(\pi)U_\pi
\tag{7.1}
\]

is self-adjoint and idempotent by finite group reindexing, with range \(\mathscr F_N\). This also proves the range closed. The earlier Lean closedness result is consistent with this paper construction; it does not already assert every domain fact below.

For smooth vectors, direct chain rule gives

\[
D_{i,\alpha}U_\pi\psi
=U_\pi D_{\pi^{-1}(i),\alpha}\psi.
\tag{7.2}
\]

Smooth H^k approximation extends this to weak derivatives through order two. In particular U_π preserves H¹ and H², commutes with Δ on H², and is an isometry for the norms used here. It follows that \(\mathcal P_-\) is bounded on both Sobolev spaces and maps compact smooth spin vectors to compact smooth ones. Apply it to an H^k-approximating sequence of ψ∈H^k∩\(\mathscr F_N\). This proves density of the compact smooth fermionic vectors in both H¹∩\(\mathscr F_N\) and H²∩\(\mathscr F_N\); their L² density in \(\mathscr F_N\) follows from the same argument with k=0. Thus the intended operator domain is dense.

The potential is invariant under P_π: nuclear terms are reindexed; the unordered pair set is permuted and reversing an order leaves a norm unchanged. With the zero convention this holds at collisions as well; almost-everywhere invariance would suffice. Thus VU_πψ=U_πVψ for H¹ ψ. Together with (7.2), this gives HU_πψ=U_πHψ on H². If ψ is fermionic, its output h is fermionic. Therefore the graph in §6 has exactly the intended input domain and output space.

The fermionic space is nonzero for every finite N. Choose N normalized compact smooth one-particle spatial functions with mutually disjoint supports, and give each the same spin-up label. They are orthonormal spin orbitals. Their normalized determinant, divided by √(N!), is a nonzero compact smooth N-electron spin vector with the required simultaneous antisymmetry and norm one. Its disjoint supports may be chosen away from the origin. This argument does not limit N to the number of spin labels.

## 8. Direct self-adjoint realization, with the exact domain

By (3.2), Fourier conjugation identifies A on weak H² with multiplication by the real function a(ξ)=|ξ|²/2, componentwise in spin. A real multiplication operator on the domain {f:af∈L²} is self-adjoint: testing its adjoint against L² functions supported on {|a|≤m} shows that the adjoint output must be af and that af∈L². Hence A is densely defined, nonnegative and self-adjoint, with exactly the weak H² domain.

On that domain B=V is symmetric, because V is real and Bψ∈L². Take ε=1/2 in (1.3), so

\[
\|B\psi\|\le\tfrac12\|A\psi\|+b\|\psi\|,
\qquad b=C_{N,Z}^2.
\tag{8.1}
\]

For either z=it or z=−it, t>2b, the Fourier multiplier R_z=(A−z)⁻¹ exists and

\[
\|R_z\|\le t^{-1},\qquad \|AR_z\|\le1,
\qquad \|BR_z\|\le\tfrac12+b/t<1.
\tag{8.2}
\]

Its range is D(A), since AR_z is bounded and (A−z)R_z=I. The Neumann series for I+BR_z converges in bounded-operator norm. For H=A+B with domain D(A),

\[
H-z=(I+BR_z)(A-z),\qquad
(H-z)^{-1}=R_z(I+BR_z)^{-1}.
\tag{8.3}
\]

Thus H±it are onto, with bounded everywhere-defined inverses. H is symmetric and densely defined. Here is the exact adjoint argument: given y∈D(H*), choose x∈D(H) with
\((H-it)x=(H^*-it)y\). Then y−x∈ker(H*−it), and that kernel equals Ran(H+it)^⊥={0}. Consequently y=x∈D(H), proving H*=H. This proves self-adjointness on the domain already identified as weak H², rather than merely the existence of some unspecified extension.

The projection \(\mathcal P_-\) preserves D(H) and commutes with H there. Equation (8.3), or the equation (H−z)x=f followed by \(\mathcal P_-\), gives
\(\mathcal P_-(H-z)^{-1}=(H-z)^{-1}\mathcal P_-\).
Hence for f∈\(\mathscr F_N\), the solution x also lies in \(\mathscr F_N\). The same two-surjective-ranges argument inside this Hilbert space proves that the restriction is self-adjoint on exactly H²∩\(\mathscr F_N\). Merely showing invariance without this resolvent/domain step would not have established self-adjointness of a restriction.

For quantitative graph norms, (8.1) and H=A+B imply

\[
\|H\psi\|\le\tfrac32\|A\psi\|+b\|\psi\|,
\qquad
\|A\psi\|\le2\|H\psi\|+2b\|\psi\|.
\tag{8.4}
\]

By (3.3), the H² norm and \(\|\psi\|+\|H\psi\|\) are equivalent. The compact smooth fermionic set in §7 is therefore an operator core. Its essential self-adjointness is a consequence, not an additional boundary-condition assumption.

## 9. Closed form, its exact associated operator, and semiboundedness

For f,g∈H¹ define the sesquilinear potential form
\(b(f,g)=\sum_\sigma\int V\overline f_\sigma g_\sigma\).
By (5.4),

\[
|b(f,g)|\le C_{N,Z}\|f\|G(g),\qquad
|b(f,f)|\le C_{N,Z}\|f\|G(f).
\tag{9.1}
\]

In particular these are absolutely convergent integrals and the form is H¹-continuous. No finite potential expectation is postulated. With c=C_(N,Z)²+1, Young's inequality gives

\[
\tfrac14G(f)^2+\|f\|^2
\le q[f]+c\|f\|^2
\le\tfrac34G(f)^2+(2C_{N,Z}^2+1)\|f\|^2.
\tag{9.2}
\]

The middle expression is therefore a complete norm squared on H¹∩\(\mathscr F_N\), proving this is a densely defined closed semibounded form. On H²∩\(\mathscr F_N\), integration by parts in the weak sense gives q(v,u)=〈v,Hu〉 for all v∈H¹∩\(\mathscr F_N\).

Conversely, suppose u∈H¹∩\(\mathscr F_N\), h∈\(\mathscr F_N\), and q(v,u)=〈v,h〉 for every fermionic H¹ test v. For any full-space H¹ test φ, group invariance of q implies

\[
q(\phi,u)=q(\mathcal P_-\phi,u)=\langle\mathcal P_-\phi,h\rangle
=\langle\phi,h\rangle.
\]

Take arbitrary compact smooth φ with just one spin component. This says in distributions

\[
-\tfrac12\Delta u+Vu=h.
\]

Since Vu∈L² by (5.4), Δu=2(Vu−h)∈L². By the Fourier equivalence (3.2), u is in the *actual weak* H² space, and the output agrees with H. Thus the operator associated with q, defined by its test identity, has exactly domain H²∩\(\mathscr F_N\) and is precisely the self-adjoint H of §8. This closes the form/operator-domain bridge without assuming H² regularity for a form solution.

For the useful lower bound, a compact smooth scalar f in R³ obeys

\[
0\le\|\nabla f+\alpha(x/|x|)f\|_2^2
=\|\nabla f\|_2^2+\alpha^2\|f\|_2^2
 -2\alpha\int\frac{|f|^2}{|x|},\qquad \alpha\ge0.
\tag{9.3}
\]

The calculation uses div(x/|x|)=2/|x|. Its inner sphere boundary term tends to zero like ε²; there is no delta contribution at the origin. The left side extends by ordinary H¹ convergence because x/|x| is bounded. For the right potential integral, (4.1) and Cauchy–Schwarz show H¹ continuity. Thus (9.3) holds for weak H¹. Slice and sum spins and particles, take α=Z_+, and use the nonnegative electron repulsion. If Z<0 the nuclear term is also nonnegative. In all cases,

\[
q[\psi]\ge-\tfrac12NZ_+^2\|\psi\|^2.
\tag{9.4}
\]

More generally, for 0<θ≤1 the same argument using α=Z_+/θ gives

\[
q[\psi]\ge(1-\theta)\tfrac12G(\psi)^2
 -\frac{NZ_+^2}{2\theta}\|\psi\|^2.
\tag{9.5}
\]

This bound drops repulsion only after its positive sign and integrability have been established. It would be false as a deduction for an attractive pair Hamiltonian with the same right side.

## 10. Finite spectral bottom and its variational identification

Let ψ be any normalized compact smooth fermionic Slater vector from §7. Its dilation

\[
\psi_L(x)=L^{-3N/2}\psi(x/L),\qquad L>0,
\]

is still normalized, fermionic and in H². Exact homogeneity of the uncut potential and a change of variables give

\[
q[\psi_L]=L^{-2}\tfrac12G(\psi)^2+L^{-1}b(\psi,\psi)\longrightarrow0.
\tag{10.1}
\]

This supplies nonempty finite trial values; no ground eigenfunction is used. By the self-adjoint spectral theorem, σ(H) is nonempty on the nonzero Hilbert space \(\mathscr F_N\). The lower numerical bound (9.4) implies σ(H)⊂[−NZ_+²/2,∞): if a bounded spectral window lay strictly below that number, a normalized vector in its spectral range would contradict (9.4). Hence E=inf σ(H) is finite below; any normalized trial gives a finite upper bound by the same spectral representation.

Every normalized u∈D(H) has
\(\langle u,Hu\rangle=\int\lambda\,d\mu_u(\lambda)\ge E\).
For each δ>0 the projection 1_[E,E+δ)(H) is nonzero; otherwise the spectral support would start at least at E+δ. Choose a normalized vector in its range. Its bounded spectral support puts it in D(H), and its expectation is at most E+δ. Let δ decrease to zero. This proves the operator variational equality in (1.5). Applying it to (10.1) yields E≤0. Nothing asserts that the low-window vectors converge to a vector or that E is an eigenvalue.

Finally approximate a normalized u∈H¹∩\(\mathscr F_N\) by compact smooth fermionic u_m in H¹. Their norms tend to one; normalize the nonzero tail. By (9.1), q[u_m/||u_m||]→q[u]. Since each lies in D(H), the form infimum cannot be below the operator infimum. The reverse inequality is immediate from D(H)⊂H¹∩\(\mathscr F_N\). This proves the form equality. Graph existence and uniqueness in §§6–7 then identify the project's exact EReal variational definition with the finite real E embedded in EReal.

For Z≤0, (9.4) and E≤0 give E=0; this is a spectral-infimum statement, not a binding assertion. For the physical integer inputs N,Z,p, these foundations specify the target energy and domain but do not yet compute an interval at precision p.

## 11. Checked primary/authoritative sources and access limits

The original paper is T. Kato, *Fundamental properties of Hamiltonian operators of Schrödinger type*, Transactions of the AMS 70 (1951), 195–211, [DOI and publisher page](https://doi.org/10.1090/S0002-9947-1951-0041010-X). The publisher PDF request returned HTTP 403 on 2026-09-09; the original full text was **not** available for a line-by-line check here. No conclusion above depends on pretending it was read.

The [author-hosted Teschl text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), version dated February 12, 2009, was accessed. Theorem 7.5 and §7.1 provide Fourier unitarity and weak Sobolev equivalence; Theorem 6.4 assumes a symmetric perturbation with relative bound below one; Theorem 11.1 treats real potentials depending on orthogonal coordinates, with transverse dimension at most three, and gives H² domain and a compact smooth core. Theorem 2.19 identifies the spectral infimum with the operator Rayleigh infimum. These statements match the uses made here. The book's kinetic normalization is −Δ; the factor 1/2 was tracked explicitly in §§6–9. The source check is for applicability, not evidence of novelty or Lean completion.

The concrete Coulomb argument in §§2–10 was written out from the stated foundations. It does not derive the three-electron or arbitrary-N analytic approximation chain from two-electron isolated-collision estimates. In particular, nullity of intersecting collisions does not imply the all-order regularity estimates needed near those strata.

## 12. Formalization interfaces and remaining status

| Interface | Exact obligation exposed by this paper | Current evidence in this file |
|---|---|---|
| Collision nullity | `volume {x | not collisionFree x}=0` for every N | Paper proof §2; any separate Lean theorem must be audited independently |
| Weak H¹/H² bridges | Smooth approximation and Fourier equivalence for the existing real-test definitions | Paper proof outline using classical Fourier/mollifier infrastructure, §3 |
| Hardy multiplication | Actual measurable inverse-distance product is L² for H¹ and satisfies (5.1),(5.2) | Paper proof §§4–5 |
| F02 output existence | For every ψ in `targetDomain`, exactly one h satisfies `hamiltonianGraph` | Paper proof §§6–7; no formal completion asserted |
| F03 realization | Dense operator with the exact graph, adjoint domain equality, fermionic restriction | Paper proof §§7–8; no formal completion asserted |
| F04 energies | Closed H¹ form; its operator is the graph; finite variational equals actual spectrum | Paper proof §§9–10; no formal completion asserted |

The next executable formal tasks are the continuum Hardy bridge, weak Sobolev/Fourier correspondence, and a domain-aware unbounded resolvent construction in the declared Lean environment. A conditional Lean structure carrying these statements as fields would not discharge them. All-order regularity, approximation, spectral separation, verified finite computation, termination and bit complexity remain separate obligations.
