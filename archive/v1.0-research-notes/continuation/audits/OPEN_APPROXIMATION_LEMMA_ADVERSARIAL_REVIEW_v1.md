> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# OPEN approximation lemma: adversarial review, version 1

Date: 2026-09-10. Canonical review requested in the priority attachment.

**VERDICT: PROVABLE AS STATED.**

This verdict concerns the precise **fixed-charge atomic dyadic approximation statement OA below**, at **paper-proof level**. The reviewed continuation proves the stronger rate exp(−c n^(1/3)) for the unchanged dictionary; it therefore supplies the originally requested exp(−c n^(1/16)) approximation as a weaker consequence. The verdict does not say that OA, its analytic dependencies, the algorithm, either cost exponent, or full Theorem T is Lean-verified. It does not discharge the distinct correlated-Gaussian OPEN lemma. No physical counterexample or new mathematical failure requiring a weaker rate was found. The proof route and the concrete attempted breaks, rather than reviewer agreement, support this assessment.

The current compiling KS units were finished and sealed before the switch. No new regularity module or isolated rebuild was begun during this review. One final Colab observation timed out without returning state; its result is **unobservable**, not a successful or failed job. It was not retried or relaunched. Existing seals remain unchanged.

Frozen base: `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. This is a new review under its correction protocol. The source inventory at the end identifies reviewed bytes and reading scope.

## 1. Reconciliation in the requested source order

### 1.1 The helium skeleton's OPEN lemma

`HELIUM_CERTIFICATION.md`, “The single OPEN lemma,” equation (2), is a **stable correlated-Gaussian H¹** conjecture. It is not an H² statement. Its input class consists of two electrons and one or two fixed nuclei, with fixed charge and geometry bounds and promised simple ground state, spectral gap and ionization margin. Binary input length is L. It asks for explicit integers a,d and a deterministic algorithm D, depending only on those class constants, such that at precision p:

* Q=a(L+p+1)^d bounds the number m of columns and their rational parameter height h, with L+1≤h≤Q, and D costs at most Q²;
* the exponent matrices are rational positive definite 2×2 matrices with eigenvalues in [2^(−h),2^h], and the centers are rational;
* some real coefficient vector c satisfies Σ|c_j|²≤2^h and H¹ error at most 2^(−p).

The columns are normalized Gaussian primitives before the simultaneous fermionic projection. Projected columns can be redundant or zero. The coefficient inequality is a real magnitude bound, not a finite binary encoding of those real coefficients. Its form regularization is a different certification method. No generator D or reduction proving this stable molecular Gaussian claim was found in the dyadic papers.

### 1.2 The later atomic target

`TWO_ELECTRON_THEOREM.md` records an earlier conditional RATE-to-cost program and a fixed-finite-exponent obstruction. `RWA_REPORT.md` and `rwa_proof/THEOREM_T_COMPOSITION.md` later fix the expanding dictionary

\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
 e^{-Z2^jS}\mathcal P_{n-2j}^{\rm sym}(r,s,u),
\qquad S=r+s,
\]

where r=|x₁|, s=|x₂|, u=|x₁−x₂|, and the polynomials have ordinary nonnegative integer powers and are invariant under r↔s. The spin factor is the unit singlet. There is no added logarithm, cusp factor, compact cutoff, Gaussian exponent, or additional exponent node in the final vector. The physical Hamiltonian is

\[
H_{2,Z}=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u
\]

on the actual weak H² domain intersected with the full simultaneous spatial/spin fermionic space. Electron count N=2, order n, and precision p are distinct. The frozen auxiliary notation “N=n+2” is written ν_n=n+2 here.

These are **two separate results**, with different input classes, dictionaries, norms and certification methods. No reduction between them has been proved. **T02 composes the fixed-charge atomic dyadic result.** The Gaussian lemma remains separately open and deferred from this reduced critical path. The fixed-finite-exponent obstruction does not apply to nodes whose maximum increases as Z2^floor(n/2).

### 1.3 The actual-eigenfunction continuation

`ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md` composes actual H² eigenfunction, symmetry and exponential tail inputs with PDE-derived uniform analytic estimates and `ENDPOINT_ONE_THIRD_v3.md`. Its exp(−c n^(1/3)) result uses exactly V_n^(Z) above. Its root review correctly distinguishes that existence proof from a procedure that computes its particular coefficients. The finite dyadic solver can use a different rational vector in the same span; Section 5 explains why the missing coefficient selector is not a mathematical obstruction to that route.

The assertion that the lemma had never been adversarially reviewed after the freeze is not supported by the checkout. The prior approximation audit, computation/spectral audit, endpoint review and actual-eigenfunction root review are preserved and included in this reconciliation. This review adds renewed independent checks and explicit countermodels; it does not relabel the previous audits as absent.

### 1.4 The four ledger entries and the actual present boundary

The reviewed ledger snapshot is preserved byte-for-byte as `OPEN_APPROXIMATION_LEDGER_INPUT_v1.json`. A02_D01_new_rate still marked the physical ground/symmetry/tail inputs undischarged; A03_exterior_decay still requested the physical comparison instantiation. Later sealed formal checkpoints supersede those particular frontier descriptions. They establish the actual two-electron ground branch, real singlet spatial structure, rotation/exchange symmetry, exponential full H² tails, boundedness and locally Lipschitz representative. The actual representative is smooth off collisions. In particular the available formal total-radius tail rate is Z/(16√2); a stronger paper constant is not silently substituted for it.

F02–F04 also have completed formal continuum results in the continuation. They are not reopened by this review. For every real Z≥2 the current ground comparison gives E_Z≤−9Z²/14 and the rest of the actual spectrum is separated by at least Z²/56. The selected nuclear KS weak equation and its local weak H² gain are now formal. These facts do **not** already give uniform factorial G1/G2 bounds.

T02 correctly remains unverified. Its exact-dictionary synthesis, all-order approximation, moments/heights, implementation and operational bit-cost chain are unfinished. The frozen mean filter additionally uses the specific bound U_Z=−Z²+5Z/8 and strict E_Z<U_Z; the newer formal bound E_Z≤−9Z²/14 must not be mistaken for a proof of that particular filter margin. No acceptance schedule is changed here.

## 2. One precise OPEN statement: OA

For every fixed integer Z≥2, let E_Z=inf spec(H_{2,Z}) for the actual operator above. Let ψ_Z be the normalized real spatial ground function with the established rotation/exchange symmetries, so ψ_Z times the unit singlet is an actual ground vector. Fix its sign, for example by positive overlap with the hydrogen product; pointwise positivity at a collision is unnecessary.

Use the physical Sobolev norm

\[
\|f\|_{H^2_*}^2=\|f\|_2^2+
 \sum_{a=1}^6\|\partial_a f\|_2^2+
 \sum_{a,b=1}^6\|\partial_a\partial_bf\|_2^2.
\]

Construct the basis Φ_(n,i), 1≤i≤m_n, by enumerating each exchange orbit of monomials once, summing its distinct monomials, dividing its degree-d sum by d!, multiplying by e^(−Z2^jS), and choosing a rational power-of-two scaling so its **reduced** squared norm lies in [1/2,2]. This is the frozen effective basis convention; the common angular factor 8π² is omitted from all three reduced matrices G_n,A_n,Q_n. In particular actual physical norm squared equals 8π² cᵀG_nc. The spin factor has norm one.

Define the integers

\[
\nu_n=n+2,\quad z_Z=1+\lceil\log_2(Z+1)\rceil,\quad
H_Z(n)=2^{40}(z_Z+1)^2\nu_n^3,\quad
h_Z(n)=2^{46}(z_Z+1)^2\nu_n^{11}.
\]

**OA:** There are constants C_A(Z)>0 and c_A(Z)>0, independent of n, such that for every integer n≥1 there is a real vector c_n with

\[
u_n=\sum_{i=1}^{m_n}c_{n,i}\Phi_{n,i}\in V_n^{(Z)},\qquad
\|u_n\|_2=1,\qquad
\|u_n-\psi_Z\|_{H^2_*}\le C_A(Z)e^{-c_A(Z)n^{1/3}}.             \tag{OA1}
\]

The deterministic basis generator takes only (Z,n), has m_n≤ν_n⁴, and has the frozen polynomial bit-size and O_Z(ν_n^16) generation bounds. The **actual** reduced Gram matrix is rational positive definite, its rational numerator and denominator heights are at most H_Z(n), and

\[
\lambda_{\min}(G_n)\ge
 2^{-m_n^2H_Z(n)}(2m_n)^{-(m_n-1)}\ge2^{-h_Z(n)}.               \tag{OA2}
\]

Consequently Σ_i c_(n,i)²≤2^h_Z(n); this also holds for every reduced-normalized vector. No extra conditioning promise is an input. The physical normalized vector has cᵀG_nc=1/(8π²)<1, so the displayed bound is conservative in that normalization.

For a precise rational bit-height consequence, put b_Z(n)=H_Z(n)+2z_Z+20 and

\[
t=p+b_Z(n)+\lceil\log_2m_n\rceil.
\]

For every p≥1 there exists q∈(2^(−t)ℤ)^m_n with

\[
\left\|\sum_iq_i\Phi_{n,i}-\psi_Z\right\|_{H^2_*}
 \le C_A(Z)e^{-c_A(Z)n^{1/3}}+2^{-p-1}.                        \tag{OA3}
\]

Each q_i has denominator bit length at most t+1 and signed numerator bit length at most t+⌈h_Z(n)/2⌉+2. This is **existence of a finite rational representation**, with height O_Z(ν_n^11+p). It is not a program given ψ_Z or its unknown coefficients. Normalizing this rational combination is represented by division by its physical norm; the normalized coefficients need not be rational. The distinct finite solver has rational common-denominator witness height O_Z(ν_n^15), subject to its own algorithm proof.

All conclusions OA1–OA3 are paper results here. In particular the basis generator and bit bounds describe an actual finite mathematical procedure, but its complete operational implementation is not verified in this project. The exponent 1/3 is the separately versioned continuation strengthening, not a silent edit of the frozen theorem. For n≥1, OA1 implies the original 1/16 rate with the same C_A,c_A.

### Named analytic constants and their dependence

The rate proof consumes the following finite data, all for this actual fixed-Z branch:

* σ=1/2; a vertex radius δ_v>0; factorial constants C_v,A_v>0 for f=ψ̂_Z−ψ_Z(0), with |∂^ηf|≤C_v A_v^|η||η|! S^(σ−|η|), including compatible nonvertex boundary germs (G1).
* d with 0<d<δ_v/8; an exterior radius constant H_d>0 and amplitude M_d<∞, giving compatible germs of ψ̂_Z on D(x,H_d/(1+S(x))) bounded by M_d for S(x)≥d (G2).
* a tail prefactor C_t<∞ and γ_Z=Z/(16√2)>0 with the actual full-Hessian H² tail bounded by C_t e^(−γ_Z R), R≥1 (G3).
* the local Lipschitz amplitude L_Z^loc on a fixed ball about zero, a_0=ψ_Z(0), Λ_Z=L_Z^loc+|a_0|, and global bound M_Z. Their finiteness is proved for the actual representative. The particular numerical Lipschitz constant and the finite Mathlib Sobolev coefficient underlying M_Z have not been evaluated.

`PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md` P6–P24 gives C_v,A_v,δ_v from Z,|E_Z|, fixed geometry and Λ_Z. `EXTERIOR_DISTANCE_ANALYTIC_v1.md` X4–X19 gives H_d,M_d from Z,|E_Z|,d and M_Z. Neither local analytic PDE theorem assumes a discrete spectral gap. The actual branch and G3 require their separately proved spectral/exterior-coercivity inputs. No claim is made uniform over arbitrary states with shrinking decay margins or over unbounded Z.

For the endpoint construction let h_T=c_h/(1+T)², with c_h>0 supplied by the G1/G2 shell restriction, and M_h its uniform rescaled amplitude. Its universal fitting exponent is b=log(4)/(48·50000); write b'=bc_h. Let C_E be the finite constant in E15 obtained from the stated fitting, physical norm and Poisson-tail inequalities with these data. It is a proof-level finite constant, not an evaluated numerical input. One may set

\[
\eta=\min\{b'/(4\,2^{2/3}),16,\gamma_Z/16,
                     128(\sigma+1)\log2\}>0,
\quad c_A=\eta/(2\,1538^{1/3}).
\]

The finite threshold q₀≥1 is chosen to satisfy E13 with T=(q+1)^(1/3), k=J=256(q+1) for all q≥q₀. E15 then has bracket at most 4e^(−ηq^(1/3)) and prefactor at most 257³2⁸(q+1)^(50/3). For q≥1, replace (q+1)^(50/3) by at most 2^(50/3)q^(50/3). Absorbing the resulting degree-50 polynomial by sup_(x≥0) x^50e^(−ηx/2)=(100/(eη))^50 supplies a finite unnormalized prefactor. Enlarge q₀ further until that unnormalized error is at most 1/2. Above this threshold divide by the actual L² norm, changing the H² error by at most 2(1+K_Z), where

\[
a_Z=4Z+2,\qquad K_Z=(6a_Z^2+2)(Z^2+1)
\]

bounds the actual unit eigenfunction H² norm by graph coercivity. For the finitely many remaining n≥1 choose the normalized anchor (Z³/π)e^(−ZS), which is already in V_n. Enlarge C_A to cover its finite H² distance from ψ_Z at those indices. The zero vector used for small indices in the unnormalized endpoint theorem is never divided by its norm. This defines an admissible C_A. The proof does not present a computed universal numerical C_A or a charge-uniform complexity multiplier. These existential constants suffice for the fixed-Z asymptotic theorem; they do not supply the Gaussian proposal's explicit uniform a,d.

For the frozen posterior solver, the separate spectral constants are L_Z=−Z², U_Z=−Z²+5Z/8, β_Z=−5Z²/8, g_Z=β_Z−U_Z=Z(3Z−5)/8>0 and μ_Z=U_Z−E_Z>0. The Gram lower bound, rounding height and added rounding error have no gap dependence; OA3 inherits the analytic rate constants. The stopping estimate depends on C_A,c_A and on g_Z,μ_Z. An ionization threshold is not substituted for β_Z. No unknown analytic constant is an input to the adaptive dyadic finite solver.

## 3. Proof assessment of the global analytic step

The root read the endpoint argument and the physical local/exterior, finite H12 and factorial arguments; independent agents separately attacked the endpoint/physical norm, vertex/Fock, exterior, and constructive coefficient parts. Their source-scoped notes are included in the inventory. The root checked their concrete countermodels and the important degree, norm, scaling and denominator calculations. This does not imply every primary source or every transitive Lean source was reread in this bounded review.

For N=2, any two of r=0,s=0,u=0 intersect only at the triple vertex. Normalization by S removes that vertex; it does not assert analyticity at it. On the fixed shell the three pair strata are separated. The actual weak KS equation, bounded pullback and quantitative weak gain give H12 uniformly. The factorial recurrence R13–R25 lowers its explicit derivative cost, uses only first and second cutoff derivatives, and closes a finite geometric sum. The root checked that no high derivative of v is assumed on its own right-hand side. Finite smoothness licenses the operations; the independently bounded H12 norm initializes their **uniform** constants.

Quantitative descent then gives A(X,t)+|X|B(X,t), with the correct degree of B. SO(2) invariant series cover zero triangle height, while planar square roots are used only after a positive height bound. The local and exterior chart constructions agree on full-dimensional real physical neighborhoods, including a radial margin. Their overlap arguments therefore apply to three ambient complex variables. Exterior shortest-separation coordinates cost one power of 1+S; rescaling to the fitting shell costs two. These are the actual sources of G1/G2, not an appeal to qualitative analyticity.

E2–E12 supplies a finite C^m extension and a single polynomial. At each point at most 125 cutoff supports contribute jets; the number of all charts does not enter the derivative base. The Stirling bound S(r,j)≤binom(r,j)r^(r−j) avoids an extra factorial in the cosine composition. With D=floor(q/3) and m=floor(hD/(4·50000)), the C² Fourier/Chebyshev tail is bounded by a constant times M D⁷4^(−m)/(m−7), while the same polynomial has total degree ≤q and exterior growth bounded by CM(q+1)⁷(6t)^q. The low-hq case retains h^(−2). No analytic compactly supported function is claimed.

The Poisson-window construction uses k=J=256(q+1) and has exact native index 769q+770. Telescoping leaves the exterior omitted target **ψ**, not ψ−ψ(0). The upper tail of the actual polynomial retains its (6t)^q growth. The largest squared physical volume power is 19+2σ≤21, and the remaining integral is exactly 2²²/(2k−2q−22). The exponential Poisson decay dominates this polynomial growth. Inner derivatives keep the vanishing factor (4t)^(k/2). Cartesian H² conversion treats inverse individual distances by their integrable angular weights and Hardy; the same physical vector satisfies the global estimate.

There is no hidden collision distribution in this paper passage: remove pair tubes on compact annuli with a vertex ball held fixed, then remove the vertex ball. The relevant pair flux is O(ε²), and the second vertex flux is O(δ^(σ+4)), so both vanish. Noncollision collinear faces are ordinary smooth physical compositions. Taking T=(q+1)^(1/3) balances q/(1+T)² and the exponential physical tail. This proves the stated 1/3 rate. Normalization and the actual graph estimate transfer it to a continuum residual; identifying E_Z with the spectrum uses the separately established operator/ground theorem.

## 4. Explicit adversarial attacks and outcomes

1. **H¹ does not imply H² or a residual bound.** For nonzero smooth compactly supported χ away from collisions, w_k=k^(−3/2)χe^(ikx_(1,1)) has H¹ norm tending to zero and H² norm tending to infinity; x_(1,1) is one Cartesian coordinate of the first electron. Its Coulomb residual also diverges. Thus the Gaussian H¹ lemma cannot simply be read as OA1. Its form method intentionally has a different norm requirement.

2. **Smoothness, symmetry, punctured analyticity and decay do not imply G1.** Let ρ=|X| in ℝ⁶ and Ψ=C e^(−ρ²)[1+exp(−exp(ρ^(−2)))] for ρ>0, with the bracket set to 1 at zero. It is positive, normalized, symmetric, globally Lipschitz, C∞, analytic off zero, and has exponential H² tails. The perturbation is flat at zero. On a=b=0,c=t, its continuation contains exp(−exp(1/(2z²))). At z_t=(t^(−2)+2πi)^(−1/2), displacement is O(t³), but this factor equals exp(exp(1/(2t²))). G1 would imply a bounded Taylor extension on a radius proportional to t, a contradiction.

3. **Even entire analyticity and exponential H² tails do not imply G2.** Set q=|X|² and Ψ=e^(−q²)(2+sin(e^q)). It is positive, symmetric, globally Lipschitz, and every exponential H² weight is integrable. At perimetric center (t,t,t), let Q=8t² and θ=min(H/4,1/4). For all sufficiently large t the point z_t=(t,t,−t+sqrt(4t²+iθ/2)) lies within H/(1+4t), but q(z_t)=Q+iθ. Its modulus is at least e^(−Q²+θ²)[sinh(e^Q sinθ)−2], which diverges. Analytic uniqueness prevents choosing a different bounded germ. Both this example and item 2 are smooth and nonzero at an isolated nuclear collision; a bounded Laplacian cannot cancel −ZΨ/r there. They do not solve the Coulomb equation and do not refute its G1/G2 theorem or establish a lower bound against V_n.

4. **The particular Fock coefficient cannot be inferred from the weak weighted bound.** In physical kinetic normalization it is κ_Z=Z(2−π)/(3π). The primary finite leading-log factorization gives this after y=2x; the extra log(4) quadratic term is smooth. If ψ(0)≠0, a wrong κ leaves a nonzero q log(ρ²) term with an unbounded Hessian, so it cannot yield the stronger C^(1,1) extraction. Nevertheless every finite κ satisfies the weaker weight-one estimate used in the continuation. The direct ψ approximation needs neither κ nor a convergent infinite physical Fock expansion. Morgan's full paper was inaccessible; its observed abstract does not fill an unproved physical expansion step. No such step is used here.

5. **A known literal source error remains excluded.** The degree-(n−1) B coefficient cannot have the printed degree-n radial bound in the 2009 KS source: u(y)=|y|² descends to B≡1. `ISSUE_KS_SOURCE_DEGREE_v2.md` already records this and the separate constructive coefficient repair. This review uses `KS_QUANTITATIVE_DESCENT_v1.md`, whose degree bookkeeping includes that constant term. It does not revive the erroneous estimate or allege a new refutation of the headline decomposition theorem.

6. **Boundary and radius shortcuts fail.** The germs 0 and a+b+c−1 agree on the organizing surface but do not agree in an ambient neighborhood. F_h=cos(a/h), q=0, has bounded complex h-germs but C² approximation error at least h^(−2), so the low-degree prefactor cannot omit that loss. The reviewed arguments retain full real-neighborhood agreement and h^(−2). Cusp conjugation at infinity can multiply amplitudes by e^(ZS−u/2); the G2 bound for ψ is not a bound for e^(−f_cusp)ψ. The endpoint construction fits ψ directly.

7. **Analyticity does not supply the physical tail.** C(1+S)^(−4) is an H² symmetric function with G1/G2 but an algebraic L² tail of order R^(−1). G3 is separately necessary. It is supplied here by the actual eigenfunction decay theorem, not by the polynomial approximation.

8. **Span approximation does not imply coefficient stability.** Unit columns e₀ and (e₀+εe₁)/sqrt(1+ε²) contain e₁ exactly, but its coefficient norm squared is (2+ε²)/ε². Choosing ε=2^(−2^n) invalidates any polynomial logarithmic-size conclusion without an entry-height condition. That example simultaneously has exponential representation height and therefore does not contradict OA2. With H=diag(1,0), shift −1 and regularizer τ, every normalized vector with ground overlap squared ≥1/2 has objective at least 1+τ/(2ε²), whereas e₀ has 4+τ. If ε²<τ/(6+2τ), no regularized minimizer has that overlap. Positivity of regularization alone is insufficient; the dyadic proof uses the explicit witness penalty bound instead.

None of these counterexamples is presented as a physical eigenfunction counterexample. The actual proof retains the additional premises each attack shows to be necessary. No novelty claim is made for the examples or for the resulting paper theorem.

## 5. From the approximation witness to finite computation

The Gram argument is independent of the approximation argument. Distinct radial exponential-polynomial blocks are linearly independent; varying interior angular ratios then separates the polynomial coefficients. The product of all m² Gram denominators clears every determinant monomial, so det G≥2^(−m²H). Positivity and trace G≤2m give OA2. This bounds **every** normalized real witness, including one chosen noncomputably in a paper existence proof.

For OA3, the graph inequality follows from ||Vu||≤a_Z||∇u||, ||∇u||²≤||u||||Δu|| and the actual equation defining H. Absorbing half the Laplacian norm gives ||u||_(H²*)≤(6a_Z²+2)(||Hu||+||u||). Since G_ii≤2 and Q_ii is a rational linear combination of 1,log2,π² with component height H_Z(n), the actual column H² norm is at most 2^b_Z(n). Rounding each c_i to its nearest 2^(−t) multiple contributes at most m·2^(−t−1)·2^b≤2^(−p−1), and the stated numerator height follows from |c_i|≤2^(h/2). This is a new explicit paper clarification of representation size, not a computed selector.

The frozen finite algorithm instead enumerates the basis and evaluates actual moments. It uses shift s₀=−Z²−1 and

\[
D_n=Q_n-2s_0A_n+s_0^2G_n,\quad
T_n=D_n+\tau_n I,\quad
\tau_n=2^{-h_Z(n)-n-10},\quad\delta_n=2^{-n-10}.
\]

Here T_n≥G_n+τ_nI, and the reduced-normalized analytic witness pays at most τ_n2^h=δ_n. Rational interval entries and exact PSD bisection with a retained rational negative witness approximate max(cᵀG_nc)/(cᵀT_nc). The anchor gives B₀=(1+2Z)²+2 and reciprocal lower bound 1/B₀. Entry error

\[
\zeta_n=\tau_n\delta_n/
 [2^{20}B_0^2m_n^2(2+2|s_0|+s_0^2)]
\]

controls the solve and final contraction. Scaling the rational witness to max coefficient norm one leaves cᵀG_nc≥τ_n/(2B₀). The exact rational mean filter m≤U_Z, directed second moment and Temple formula then give a continuum enclosure, provided the domain, moments and separator premises are discharged. Correctness of an emitted interval does not require RATE; this proof uses RATE for eventual success.

Thus the absent chart/coefficient oracle does not break the adaptive dyadic route. Conversely none of these paper instructions, existential witnesses or finite experimental scripts is a fully verified implementation. G,A are rational; Q belongs to the **rational linear span** of 1,log2,π², not a claimed three-dimensional field. The old terminology clarification is preserved.

The stated schoolbook binary cost model charges operand sizes and uses common-denominator fraction-free elimination. At fixed Z it gives dimension O(ν_n⁴), precision O_Z(ν_n^11), matrix-entry work O_Z(ν_n^140), and the smaller PSD/witness upper cost bound O_Z(ν_n^53), with intermediate height O_Z(ν_n^15). An exponent α gives stopping order O_Z((p+1)^(1/α)); summing all stages gives 141/α. Hence 2256 for α=1/16 is the frozen **conditional paper** cost, and 423 for α=1/3 is a separately identified **conditional paper consequence**. Neither is claimed as a new full composed theorem, verified operational bound, or observed runtime. No Rung 3–6 computation was started to assess it.

## 6. Exact remaining formal obligations and reduced path

The following list records the undischarged formal bridges; a paper proof is not counted as a missing mathematical argument merely because Lean lacks it.

| Obligation | Present evidence and exact remaining bridge |
|---|---|
| R01: uniform weak initialization | Formal local weak gains and explicit cutoff estimates exist. Compose them into the numerical H12 bound, with a common coefficient/source derivative budget and boxes independent of collision scale. Membership alone is insufficient. |
| R02: factorial recurrence | Paper R13–R25 is checked. Formalize weighted derivative families, finite tangential/y recovery, commutators, cost decrease, fixed-gap recurrence and pointwise Taylor convergence. Do not assume smooth or analytic conclusions as input. |
| R03: both physical KS charts | The actual nuclear chart is formal. Complete the N=2 relative/center pair chart with c=1, its weak identity and removable fiber, and instantiate scaled difference and unscaled exterior equations. |
| R04: coefficients and descent | Formalize common complex reciprocal-distance branches, coefficient/source factorial bounds, circle-invariant polynomial descent with the corrected B degree, and the stated quantitative radii. |
| R05: physical distance germs | Formalize the nonsingular factorial estimate, SO(2) invariant-series boundary maps, separated normalized-shell cover, shortest-separation exterior cover, and full-real-neighborhood gluing. Compose G1/G2 for the actual representative. |
| R06: one global approximation vector | Formalize the finite-order cutoff extension, cosine/Fourier/Chebyshev bounds, exact Poisson windows, native degree schedule, every tail of the same polynomial, and physical weak H² conversion/removability. Then prove OA1 and normalization. |
| R07: exact physical basis and stability | Formalize each dictionary column's actual weak H² derivatives, integral identities, linear independence, rational heights, Gram determinant bound and OA2/OA3. Reusing abstract norm or determinant lemmas does not discharge their physical instantiations. |
| R08: residual and spectral connection | Link the actual synthesized trial to the formal graph and posterior enclosure; discharge the chosen acceptance margin. Existing spectral/domain theorems are reused, not re-audited wholesale. |
| R09: verified producer and cost | Implement all-order moment evaluation, directed rounding, finite rational PSD/witness recovery and the full stage loop; prove interval correctness, every finite stage, eventual stopping, common-denominator heights and binary cost. No noncomputable selection is the implementation. |

The **weakest active analytic link** is the quantitative uniform KS initialization and all-order recurrence feeding G1/G2. Its paper proof survives this review, but the present formal chain still stops at finite gains. The largest later unverified blocks are the global polynomial construction and the actual certified implementation.

Only these regularity results remain active: bounded/Lipschitz physical amplitudes and their already-proved representative compatibility; N=2 nuclear and pair weak KS equations; quantitative finite initialization sufficient for the displayed H12 schedule; factorial KS/nonsingular elliptic estimates; quantitative descent and boundary/exterior compatible germs. The existing physical G3 tail is reused. General lemmas are justified only when directly serving this concrete route.

**Deferred A01 work:** full convergent Fock expansions, further Fock coefficients, stronger C^(1,1) extracted remainders, exact κ formalization solely for extraction, positivity at the vertex, sharper decay rates or evaluated Moser/Lipschitz constants not needed for fixed-Z termination, arbitrary-N/molecular collision analyticity, and unrelated observables/dynamics regularity. They are not consumed by OA or the selected fixed-Z solver. Completed reusable lemmas remain preserved. Rungs 3–6 stay paused until Rung 2 closes. No new broad manuscript or numerical program is authorized by this checkpoint.

No corrected theorem is required by a failed rate: no such failure was established. The existing 1/3 continuation keeps its own identity; the frozen 1/16 and 2256 claims remain formally unverified. The source-degree correction continues under its existing issue record.

**Next executable action:** compose the sealed explicit local Grushin one-step estimate, differentiated-potential bounds and nested quantitative H² recovery into a common homogeneous local H² norm estimate with no derivative norms on the right. Then use its finite tangential/y schedule toward R01. Develop only on the pinned caches, disclose their use, and retain strict expanded-statement/axiom audits. No immediate isolated rebuild is needed merely because this verdict now permits one.

## 7. Evidence, reproduction and source inventory

The formal baseline is supported by the cited sealed checkpoints and their expanded statement/axiom receipts. Standard `propext`, `Classical.choice`, `Quot.sound` are the recorded foundation; no new mathematical axiom or alternate trusted evaluator was added in this review. No compilation happened during the review itself. Development dependency caches were reused for the preceding KS units; v20 is the already completed isolated supplement with 817 targets. It reuses earlier isolated-source objects and the official compiler/core, so it is not a fresh empty-cache rebuild of everything. New units outside that supplement remain explicitly outside it.

The canonical review is supported by separately scoped analytic, constructive, Fock/vertex and exterior adversarial notes. Their agreement is not kernel proof. Primary Fournais coefficient/scope checks use the archived source text and image; Morgan's full article remains inaccessible. The web observation capture hashes only the actually observed excerpts and metadata, not entire remote pages. No novelty conclusion is inferred from source access or an unsuccessful search.

The inventory below is generated from actual reviewed files and the reviewers' source records. A file hash identifies bytes; it is not a claim to have read every line when the recorded scope is narrower. Transitive proof sources are linked by the sealed checkpoints rather than represented as newly reread. The live ledger was snapshotted before updating its current frontier.

<!-- BEGIN SOURCE HASH INVENTORY -->

Detailed reading-scope record: `audits/OPEN_APPROXIMATION_REVIEW_SOURCE_INVENTORY_v1.json`, SHA-256 `96902376197c29eab3ad9377d9f9110ec049ddb93f1c699349d49b41adc2d560`.

Paths below are relative to the workspace root unless absolute. The live ledger row describes the captured input bytes; its immutable copy has the same hash.

| Reviewed source | SHA-256 |
|---|---|
| `<agent-session-log>` | `113b9c5c363386b80ceffbe9789343b1011b6a2846317626478b703308bb49bd` |
| `THEOREM_T_FREEZE_2026-09-09_212604/CORRECTION_PROTOCOL.md` | `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3` |
| `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json` | `c01b4f3568b623795c5785282d94c734339445125a990cef054cb1706b3801b0` |
| `THEOREM_T_FREEZE_2026-09-09_212604/HELIUM_CERTIFICATION.md` | `a29ba0101875bb621aba3ad954891502e4c8b3dd613ee1634197459fab052d44` |
| `THEOREM_T_FREEZE_2026-09-09_212604/RATE_DICTIONARY_DECISION.md` | `d9d15d0412ae5c8148aeeff6e264c8a2c0ae23df8dc8324929e698652146f303` |
| `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` |
| `THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md` | `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79` |
| `THEOREM_T_FREEZE_2026-09-09_212604/dyadic_proof/EXTERIOR_CONSTANTS.md` | `db6e477f5ccdfdb06cf5edefa8059b2cbe13a9a69271017feca7c6ea0eca5409` |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2005_math-ph0312060.txt` | `cf3764fd6b2d96c449dd5330b85fa6eb00270f4c9b0d47db0b10207a465519bd` |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2005_math-ph0312060_p3.png` | `8c70a40035e726e021c5b40dd05e85a4f8812391a4e293776657bfc6e1933c83` |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/sources/regularity_fournais2009_0806.1004.txt` | `64ceb0f7a8708af5e87563c39d420a0500240f132d629c5c30f5677341fbf908` |
| `THEOREM_T_FREEZE_2026-09-09_212604/helium_research/theorem_skeleton.md` | `0d80f9e743d518b725ded4f705138716d62651313aa079ffdda708185eaddbf1` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/DYADIC_REMAINDER_ATTEMPT.md` | `bb30295c982758a93237b583a6d52d3490c49b0d8f0737036faa4e701d997b02` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/EXTERIOR_ANALYTIC_ATTEMPT.md` | `6b56710d1a0ad8d4a2bcc20021b69412c1f073961f33243b3378ff50d0c731f5` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/FOCK_SOURCE_AUDIT.md` | `22afddf6ece73481c32b98d03e8067ebe393cd28f09569f1e7de4b46f30e10ce` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/GLOBAL_DYADIC_ATTEMPT.md` | `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RESOLVED_SOURCE_AUDIT.md` | `f0f0b5e07fda02a7ccb817b7b40f8359fe571a67eb48eca1741825409214b85e` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_AUDIT.md` | `4c9e2674b8be8ca6d9bfe5a70ea019cb243ce620c175b9e5333b20fe973adea4` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_COMPOSITION.md` | `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da` |
| `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` |
| `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/approximation/APPROXIMATION_AUDIT_v1.md` | `53ba43a396ac5bbe7a8a911d6c459df39c0deeab5cc0e31fd8a48b75540f7efe` |
| `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/computation/COMPUTATION_SPECTRAL_AUDIT_v1.md` | `7fdcc35e44c4fb2a9e3c0fa2ba529b68a13f8c8f1147c9530d5dc0e2c6b4a013` |
| `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/errata/ERRATUM_001_MOMENT_SPAN_v1.md` | `007bd591382d81157a68e37ce76900216f95dd8979f6a7bc5db12992390b15b0` |
| `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/errata/MOMENT_SPAN_CLARIFICATION_v1.md` | `e28aa172042612cb9225111a0366f311c26c3beca082926346d22353e58a3ef9` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/STATUS_LEDGER_v2.json` | `5d797f382f828c7ae6fb2868d8913f9298e96b89efbec9fcf447284849a9c003` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_APPROXIMATION_ROOT_REVIEW_v1.md` | `b2d3f1625bfe31a07afd1bb01b99423c112b4a0443e4edbe9155c80a9ad2593a` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md` | `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COLAB_FINAL_STATE_PRIORITY_OBSERVATION_v1.json` | `6cd117b5d29b760da2904f5cedbb03b86892274068e33713633bc49df628fe34` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_CLASSICAL_REPRESENTATIVE_CHECKPOINT_v1.json` | `58afc2cc694bd44e58eade3ff5f2d2afa450b56ac195408b40261b19f3b23a14` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_COMPLEX_COEFFICIENT_BOUNDS_v1.md` | `a6b9361f229a29e3df2cf0e3e20552da7cfeb49dfbbf7f8f15d0112375eaa5b5` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_H2_TAIL_TRANSFER_v1.md` | `c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_LOCALLY_LIPSCHITZ_CHECKPOINT_v1.json` | `39352930c4189b5e69b2a1494533a1a1bb77a394d2134e95b30ea1b9435085c0` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_NUCLEAR_KS_LOCAL_H2_CHECKPOINT_v1.json` | `69eeca30ab42ef6b1d2f713b0acac61a43627c377a7bb1915ae5e647a333fc18` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/COULOMB_NUCLEAR_KS_WEAK_CHECKPOINT_v1.json` | `ae82d39849a72dc2db6041dbfb0b610e40e9c2703646ce63dc21cf08c7c9ce6c` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/DISTANCE_BOUNDARY_GERMS_v1.md` | `b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ENDPOINT_ONE_THIRD_INDEPENDENT_REVIEW_v1.md` | `e80dcf3ab9269fb0db240964fdcce50d362709d80400d37d15aa2e31abb4fc56` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ENDPOINT_ONE_THIRD_v3.md` | `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/EXPLICIT_GRUSHIN_CUTOFF_PRIORITY_CHECKPOINT_v1.json` | `b519f660775db99ee22010df531afa45ebe039dc474a7dedaac449eef08e997c` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/EXTERIOR_DISTANCE_ANALYTIC_v1.md` | `e6fdf92081e37aadd515d7badc65bf632ccfead811b388fc148d169b31183360` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/GRUSHIN_FACTORIAL_RECURRENCE_v1.md` | `5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/GRUSHIN_FACTORIAL_ROOT_REVIEW_v1.md` | `0b6f812fb9959f85f03966ef92f21a031313153dc2611909c0294b2eb1371ec4` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/GRUSHIN_H12_WEAK_INITIALIZATION_v1.md` | `ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/ISSUE_KS_SOURCE_DEGREE_v2.md` | `44abbb70c9ca98714b2b960cdd19a83dad9e761cf428abc8f7c2bc1c1a3086c2` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/KS_QUANTITATIVE_DESCENT_v1.md` | `17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/KS_WEAK_REMOVABILITY_v1.md` | `ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/LOCAL_WEAK_GRUSHIN_EXPLICIT_ONE_STEP_LOCAL_DATA_CHECKPOINT_v1.json` | `ccdad1cf54547ef519fdd14cb9fee60ed9be11117b93a130a8151a6f390507f1` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/LOCAL_WEAK_GRUSHIN_SPECTATOR_H2_CHECKPOINT_v1.json` | `9785b986ea43691e4b965cd284607fd9d9c04f9c12db7cfb7fde43599f5abb67` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md` | `d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_ANALYTIC_ADVERSARIAL_SUPPORT_CHECKPOINT_v1.json` | `661de3285ccdcec9388f81ec84e9a5891897cc0bab656e0c3261d4081fc35077` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_ANALYTIC_ADVERSARIAL_SUPPORT_v1.md` | `5cd6a1da963eeb8171e8e98769b7f94359f2c4c2dc4038a7b7064007a5179214` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_FINGERPRINTS_v1.json` | `9ea13db4d4d6de39e81fe19ca3b561d8147e04e54291b2f8850fbb30a539d352` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_CONSTRUCTIVE_COEFFICIENT_REVIEW_v1.md` | `0d20d83eb6b8de92590b7492f3ffd7aa4bade2beb75f18a153b5c6a623c871eb` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_EXTERIOR_DEPENDENCY_REVIEW_v1.md` | `1a5402f4f30cd542a2a06790cdda0302cd30f9bd2951584653866f5cfbaef619` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_FOCK_AND_VERTEX_DEPENDENCY_REVIEW_v1.md` | `bfffc209567d368d70b450a62b044cb36e583762462512e71383ec8faa7faf19` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_FOCK_VERTEX_WEB_OBSERVATIONS_v1.json` | `0bda10b6e94c15c5f4759184ebbe76a24b2a91a17d203acb8b2bab6f09676f43` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_LEDGER_INPUT_v1.json` | `5d797f382f828c7ae6fb2868d8913f9298e96b89efbec9fcf447284849a9c003` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_RATIONAL_ROUNDING_CHECKPOINT_v1.json` | `393706f199585c2c54d3ec378cc395c0ac2d52097d8afc8129d0d73cf2c5bd76` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/OPEN_APPROXIMATION_RATIONAL_ROUNDING_LEMMA_v1.md` | `4d7cc346df59e62a57de4c5c75af0f14951e4711f2c88fc53af9fce3fb442f2f` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_GROUND_BRANCH_CHECKPOINT_v1.json` | `6308dff543b48303ef542244a31b5f1e477dfdcc6414edfda78a119c51401d6b` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_GROUND_ROTATION_CHECKPOINT_v1.json` | `7eed965fde9f42a40fa48be5235f08243baa9bd4f15a0f78831f1e330b0aba54` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_GROUND_STRUCTURE_CHECKPOINT_v1.json` | `5d259f2891b5e0aa5f9cbb2ea1fa511e6a82d819e9c64acf0240cd2c8b6b52d5` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_H2_DECAY_CHECKPOINT_v1.json` | `60574ca5e7a0dc2f1dc53a1e21d9347bf7802617b2ac5cc07c2c13dd37d0707f` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md` | `8e65d5d7053012e7b40d891f9a310794aa446f87dde902770a9c13ffe4635f3e` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/QUANTITATIVE_H2_INFLIGHT_PREREQUISITES_DEFERRED_CHECKPOINT_v1.json` | `dd476e0bebf0a5a1b82aa6d8324fde18350f261d2179d7b36f250eb681184414` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/SMOOTH_CUTOFF_RESCALING_CHECKPOINT_v1.json` | `c3a7e4f7bbeb9d13fc4677e7b1f18fcaf7693de2e85342cdc3df20d0a84ec896` |
| `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/logs/reproduction/SOURCE_REBUILD_CHECKPOINT_v20.json` | `b00ee3dde69fcc443a9cc9252712611ddd915a2b140677af28630f7f9467b05c` |
