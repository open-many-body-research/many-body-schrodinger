> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

> ⚠️ **This report's "THEOREM T STATUS: PROVEN" is withdrawn.** See [ERRATUM-001](../../../errata/ERRATUM-001-theorem-t-not-proved.md).

# Physical remainder weighted analyticity and the dyadic dictionary

Date: 2026-09-09. The older project reports are retained unchanged as historical records. Status changes here are supported by the new proofs linked below. All new analytic and approximation results are **PROVEN (paper proof)**, not Lean-checked. No numerical RATE experiment, helium rerun, molecular computation, or new Lean build was performed.

## 1. The requested weighted analyticity statement

For every fixed integer \(Z\ge2\), the actual normalized positive spatial ground state of
\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u
\]
has the remainder prescribed in the request,
\[
\mathcal R_Z=e^{ZS-u/2}\psi_Z-\frac{Z(2-\pi)}{3\pi}\psi_Z(0)q\log(r^2+s^2).
\]
There are \(\delta,A,C>0\), depending only on this fixed atom, such that
\[
\left|\partial^\nu(\widehat{\mathcal R}_Z-\psi_Z(0))(a,b,c)\right|
\le CA^{|\nu|}\nu!\,S^{1-|\nu|}
\quad(\nu\in\mathbb N_0^3,\ a,b,c\ge0,\ 0<S<\delta).
\tag{1}
\]
Here \(r=b+c,s=a+c,u=a+b,S=a+b+2c\), and boundary derivatives are those of the compatible analytic germs. Thus the exact requested RWA holds with \(\sigma=1/2\), after taking \(\delta\le1\), since \(\nu!\le|\nu|!\). The stronger power one is a consequence of the proof, not an assumed strengthening of the target.

The complete proof is [RWA_THEOREM.md](rwa_proof/RWA_THEOREM.md), with the independently checked uniform operator estimate in [UNIFORM_ANALYTIC_AUDIT.md](rwa_proof/UNIFORM_ANALYTIC_AUDIT.md). Its central step estimates the actual scaled difference \((\psi_Z(\varepsilon X)-\psi_Z(0))/\varepsilon\) on a fixed shell. Lipschitz regularity bounds only its amplitude. A uniform factorial induction for the lifted equation supplies all its higher derivatives. Quantitative KS descent and rotational invariance then yield ordinary perimetric analytic radii proportional to \(S\), including every nonvertex boundary stratum.

## 2. Primary sources and exact applicability

The bounded source audit preceded the new proof. Each record gives the verified theorem number, hypotheses, spaces, dimension, collision treatment, order of regularity, and constant/uniformity limitations:

- [KS_SOURCE_AUDIT.md](rwa_proof/KS_SOURCE_AUDIT.md): the usable isolated-pair structure and factorial induction.
- [RESOLVED_SOURCE_AUDIT.md](rwa_proof/RESOLVED_SOURCE_AUDIT.md): resolved many-particle geometry, weighted Sobolev estimates, analytic corner theorems, and their precise operator mismatches.
- [FOCK_SOURCE_AUDIT.md](rwa_proof/FOCK_SOURCE_AUDIT.md): what is verified about logarithmic expansions, inaccessible sources, and the deliberate higher-logarithm test.

The load-bearing external analytic results are Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen, Theorem 1.1, [math-ph/0312060](https://arxiv.org/abs/math-ph/0312060), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6); Grušin, Theorem 5.1 and Proposition 5.1, especially (5.5), (5.14), (5.20)–(5.24), DOI [10.1070/SM1971v013n02ABEH001033](https://doi.org/10.1070/SM1971v013n02ABEH001033); and Fournais et al., Lemma 4.3 and Proposition 4.4, [0806.1004](https://arxiv.org/abs/0806.1004), DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5).

The published qualitative assertions alone do not give scale uniformity. The new operator proof supplies a common oscillator maximal estimate, small-potential absorption, common finite initial derivative norms, and common inputs to Grušin's actual factorial recurrence. The common KS coefficient bounds are then passed through the quantitative descent proof. This is an instantiation of verified primary proofs with additional uniform estimates, rather than a claim that a cited theorem already states RWA.

Morgan's accessible abstract separates convergence of suitable Fock-series solutions from identification with the bound state; the full paper was inaccessible. The original Fock text and the Guo–Babuška theorem statements were not recovered. None is a proof dependency. The resolved-collision sources establish all finite weighted orders but do not bound their constants factorially. The analytic-corner and Hartree–Fock theorems address different principal operators. Their conclusions were not transferred to this problem.

## 3. The actual remainder equation and blow-up

The full derivation is [REMAINDER_EQUATION.md](rwa_proof/REMAINDER_EQUATION.md). To display the degeneracy, write
\[
\mathsf A=\frac{ac}{ru},\quad \mathsf B=\frac{bc}{su},\quad
\Theta=1-\mathsf A-\mathsf B=\frac{abS}{rsu},\quad w=rsu,
\]
\[
G=\begin{pmatrix}1+\mathsf A-\mathsf B&0&-\mathsf A\\
0&1-\mathsf A+\mathsf B&-\mathsf B\\
-\mathsf A&-\mathsf B&\mathsf A+\mathsf B\end{pmatrix},
\quad
\mathcal L=w^{-1}\operatorname{div}(wG\nabla).
\]
Its first-order vector is
\[
\mathbf b=(-1/r+1/s+2/u,\ 1/r-1/s+2/u,\ 1/r+1/s-2/u).
\]
For \(f=-ZS+u/2\), put \(\mathbf t=G\nabla f\) and
\(W=-Z^2-1/4+Z\Theta-E_Z\). The conjugated operator is exactly
\[
\mathcal P=-\tfrac12\mathcal L-\mathbf t\cdot\nabla+W.
\]
Writing \(T=r^2+s^2\), \(\kappa=Z(2-\pi)/(3\pi)\), the source is
\[
\mathcal P\widehat{\mathcal R}_Z
=\kappa\psi_Z(0)\left\{(8+2f)q/T+
[-ZqS/(rs)-u/2-Wq]\log T\right\}.
\tag{2}
\]
In these coordinates the correct polynomial is \(q=c(S-c)-ab\). An initial expansion incorrectly omitted \(-c^2\); the exact audit caught it and the displayed files were corrected. The physical definition of \(q\) and the derived operator identities were unaffected.

Under \(x=\varepsilon z\), multiplication of the equation by \(\varepsilon^2\) gives principal part \(-\mathcal L_z/2\), drift \(-\varepsilon\mathbf t\cdot\nabla_z\), and potential \(\varepsilon^2W\). The four source contributions have respectively factors \(\varepsilon^2,\varepsilon^3,\varepsilon^3,\varepsilon^4\), with \(\log T\) replaced by \(2\log\varepsilon+\log T(z)\). Subtracting the value \(\psi_Z(0)\) adds \(-\varepsilon^2W\psi_Z(0)\) to the source. All terms and signs are written out in the linked derivation.

Neither scaling nor extraction turns \(G\) into an elliptic matrix across the faces:
\[
\det G=\frac{abc(a+b+c)T}{r^2s^2u^2}.
\]
The open faces are noncollision collinear configurations: \(a=0\) means \(r=s+u\), \(b=0\) means \(s=r+u\), and \(c=0\) means \(u=r+s\). The positive axes are respectively \(r=0,s=0,u=0\). At those axes some coefficients have direction-dependent limits. No artificial boundary condition is imposed there.

The proof therefore returns to the physical equation and lifts an isolated pair. On fixed normalized nuclear charts the principal operator is \(-\Delta_y-4|y|^2\Delta_t\), with four KS coordinates and three spectator coordinates; for an electron pair the factor four becomes one. Distinct pair sets are separated on a compact normalized shell. The Coulomb pole of the lifted pair becomes an analytic constant of size \(O(\varepsilon)\), and every spectator denominator stays separated from zero. The oscillator bound and the verified factorial induction apply to these operators, including their degeneracy.

## 4. Closed-boundary and counterexample audit

The analytic-plus-distance decomposition at each pair is quantitatively uniform after scaling. Its uniqueness makes its two analytic coefficients separately rotation invariant. An \(SO(2)\)-invariant analytic series in Cartesian transverse coordinates \((x,y)\) is an analytic series in \(w=x^2+y^2\), with an explicit geometric coefficient bound. Substitution of
\[
z=(r^2+s^2-u^2)/(2s),\qquad w=r^2-z^2
\]
then works even at collinear configurations. The electron-pair formula uses the separated spectator \(|(x_1+x_2)/2|\). Smaller chart cores retain larger analytic neighborhoods; a finite cover gives a common radius. Germs agree from their values on the physical interior. These steps handle open faces, all three nonvertex axes, their adjacent charts, and uniform approach to the vertex.

Higher logarithms were not discarded. The finite-log lemma in the source audit proves that
\(S^m(\log S)^jF(x/S)\) satisfies the requested factorial bound whenever \(m>\sigma\) and \(F\) has a common bounded holomorphic angular neighborhood. In particular the inspected formal cubic logarithm and quartic double logarithm do not refute RWA. No infinite physical Fock expansion is inferred from this calculation. The PDE proof instead controls the actual solution, including any higher logarithms it has.

The audits also exhibit nonphysical functions that are smooth at the vertex and analytic at every nonvertex point but violate RWA. This rules out the tempting qualitative-regularity shortcut. Such functions are not solutions of the Coulomb equation and are not counterexamples to (1).

## 5. Exact-dictionary local consequence

For the unchanged dictionary
\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
e^{-Z2^jS}\mathcal P_{n-2j}^{\rm sym},
\]
the new local theorem gives constants \(D,C,c>0\) and \(r_n\in V_n^{(Z)}\) with
\[
\|e^{-ZS+u/2}\mathcal R_Z-r_n\|_{H^2_*(B_D)}
\le Ce^{-c\sqrt n}.
\tag{3}
\]
The norm includes all Cartesian derivatives through order two in six dimensions. The proof is [DYADIC_REMAINDER_ATTEMPT.md](rwa_proof/DYADIC_REMAINDER_ATTEMPT.md); its independent check is [DYADIC_REMAINDER_AUDIT.md](rwa_proof/DYADIC_REMAINDER_AUDIT.md). Its RWA premise is discharged by (1).

Ordinary polynomial shell approximations are combined with
\[
E_p(t)=e^{-t}\sum_{\ell=0}^p t^\ell/\ell!,\qquad
W_{j,p}(S)=E_p(Z2^jS)-E_p(Z2^{j+1}S).
\]
These windows are already finite members of the exact exponential–polynomial dictionary. With shell degree \(q\), \(p=J=256(q+1)\), the exact required native index is
\[
N(q)=p+q+2(J+1)=769q+770.
\]
Auxiliary Gevrey cutoffs are used only to construct ordinary polynomial coefficients; they are absent from the final vector. Poisson tail estimates dominate the polynomials outside their fitting shells. Physical inverse-distance integrals and weak-derivative removability justify the Cartesian \(H^2\) estimates at pair axes and the vertex.

Adding (3) to the already-proven leading-log witness stays in the same \(V_n^{(Z)}\), and proves local \(H^2\) approximation of the full physical wavefunction. The earlier leading theorem is reused without re-proving it. Local approximation alone does not yet control the same vector at infinity; the separate global proof is documented below.

## 6. Verification boundary

The exact standard-library script [audit_reduced_identities.py](rwa_proof/audit_reduced_identities.py) checks 26 polynomial identities over \(\mathbb Q[a,b,c,Z]\). Its recorded result is [reduced_identity_audit.json](rwa_proof/reduced_identity_audit.json), including the input script SHA-256 and machine provenance. It checks coordinate transformations, divergence coefficients, the conjugation identities, determinant, and logarithmic-source contractions. It uses rational arithmetic, not floating point.

This algebra check does not certify the analytic theorem. The analytic and approximation proofs are human-readable paper proofs with independent agent review. **PROVEN (Lean): no new theorem this session. EMPIRICAL: no new evidence used.** No claim of machine verification of RWA, global RATE, or the continuum operator is made.

The main avoided gaps are recorded explicitly: no inference from \(C^{1,1}\) to factorial bounds; no change of derivative weight; no isolated-point elliptic theorem applied to the degenerate reduced operator; no unverified physical Fock expansion; no arbitrary cutoff in a dictionary vector; no energy or variance rate substituted for an operator graph rate; and no unknown analytic constant used as an algorithmic oracle.

## 7. One global witness and its exterior

**PROVEN (paper).** The exterior analytic estimate and the global construction now close both globalization obligations. The independent checks are [EXTERIOR_ANALYTIC_AUDIT.md](rwa_proof/EXTERIOR_ANALYTIC_AUDIT.md) and [GLOBAL_DYADIC_AUDIT.md](rwa_proof/GLOBAL_DYADIC_AUDIT.md).

For every fixed \(D>0\), the actual reduced wavefunction at every \(S\ge D\) has a holomorphic perimetric polydisc of radius at least \(c_{Z,D}/(1+S)\) and sup norm at most \(M_{Z,D}\). The full proof is [EXTERIOR_ANALYTIC_ATTEMPT.md](rwa_proof/EXTERIOR_ANALYTIC_ATTEMPT.md). A direct Moser iteration first bounds the global real amplitude. Fixed physical Cartesian/KS charts then have uniform analytic norms because all spectator poles are uniformly separated. The distance conversion loses only a polynomial radius: \(|\Delta z|\le9\delta\), \(|\Delta w|\le102(1+S)\delta\). The audit corrected a projected electron-pair center bound from \(D/2\) to \(D/4\); this changes only a fixed chart radius. It is not an assumption about compactness of the unbounded exterior.

Here is the single global witness. Set \(f=\widehat\psi_Z-\psi_Z(0)\), \(p=J=256(q+1)\), \(T_q=(q+1)^{1/16}\), \(a_j=Z2^j\), and \(\tau_j=p/a_j\). Choose the first \(j_0\ge0\) for which \(a_{j_0}\ge p/T_q\). For sufficiently large \(q\), \(j_0\le J\) and \(T_q/2<\tau_{j_0}\le T_q\). Let \(P_j\) be the degree-\(q\) ordinary shell polynomial for \(f\). Define
\[
v_q=\psi_Z(0)E_p(a_{j_0}S)+\sum_{j=j_0}^{J}W_{j,p}(S)P_j.
\tag{4}
\]
Every term has the original nodes; \(v_q\in V_{769q+770}^{(Z)}\). With \(E_{\rm out}=E_p(a_{j_0}S)\) and \(E_{\rm in}=E_p(a_{J+1}S)\), the exact identity is
\[
\psi_Z-v_q=\psi_Z(1-E_{\rm out})+fE_{\rm in}
+\sum_{j=j_0}^JW_{j,p}(f-P_j).
\tag{5}
\]
The outer omitted function is the decaying physical \(\psi_Z\). Using a constant at the wrong outer node would leave a false constant plateau and invalidate this argument.

The global proof conservatively tracks the shell extension radius as \((1+T_q)^{-2}\), its Gevrey parameter as \((1+T_q)^8\), and a polynomial prefactor \((1+T_q)^{62}\). It proves the explicit error estimate in (G24) of [GLOBAL_DYADIC_ATTEMPT.md](rwa_proof/GLOBAL_DYADIC_ATTEMPT.md). Its terms are the shell fit \(e^{-b\sqrt q/(1+T_q)^4}\), Poisson tails \(e^{-p/16}\), the physical outer tail \(e^{-\gamma T_q/16}\), and the inner omission \([p/(Z2^{J+1})]^{\sigma+1}\), all multiplied by one tracked polynomial. Here \(\gamma=Z/(4\sqrt2)\) is supplied by the already-proven physical tail.

The upper tails of the actual shell polynomials are included. Their worst squared integral is bounded by a prefactor times
\[
12^{2q}e^{-p/2}\int_2^\infty t^{21}(t/2)^{2q-2p}\,dt
=12^{2q}e^{-p/2}\frac{2^{22}}{2p-2q-22}.
\]
The choice \(p=256(q+1)\) absorbs this growth. Localized Hardy inequalities control the inverse-distance Hessian terms in \(\psi_Z(1-E_{\rm out})\). The cutoff used to prove that Hardy estimate is not present in the witness. The large-shell norm factor \(\tau_j^{\sigma+1}(1+\tau_j^2)\) retains the zero-order scaling that a purely local estimate would miss.

It follows that, for all \(n\ge0\), there exist \(v_n\in V_n^{(Z)}\) with
\[
\boxed{\ \|\psi_Z-v_n\|_{H^2_*(\mathbb R^6)}\le C_Ze^{-c_Zn^{1/16}}.\ }
\tag{6}
\]
After normalization, using the dictionary anchor for finitely many small indices,
\[
\boxed{\ \inf_{\phi\in V_n^{(Z)},\ \|\phi\|_2=1}
\|(H_Z-E_Z)\phi\|_2\le C'_Ze^{-c'_Zn^{1/16}}.\ }
\tag{7}
\]
The norm and residual are for the actual continuum operator. The three inputs of the global theorem are discharged: (G1) follows directly from (R11)–(R14) of the new vertex proof, (G2) is the new exterior theorem, and (G3) is the frozen physical tail theorem. The explicit leading-log approximation remains valid and supplies the requested local composition; the stronger direct vertex estimate also permits (4) to approximate the full state without separating its logarithm again.

The global result is an existence and rate theorem for this exact dictionary. Its intentionally weak exponent and large constants have no asserted relation to measured finite-order rates.

## 8. Theorem T and the complete effective composition

**PROVEN (paper), Theorem T.** For every fixed integer \(Z\ge2\), there are a deterministic algorithm \(\mathcal A_Z\) and a finite constant \(C_Z>0\) such that, for every requested precision \(p\in\mathbb N\), \(p\ge1\), the algorithm returns rational numbers \(\ell_p,u_p\) satisfying
\[
\ell_p\le\inf\operatorname{spec}(H_Z)\le u_p,
\qquad u_p-\ell_p\le2^{-p},
\]
in at most
\[
\boxed{C_Z(p+1)^{2256}\text{ bit operations}.}
\tag{8}
\]
The operator acts on the full antisymmetric spin-space Hilbert space with the established \(H^2\) domain; the symmetric spatial trial dictionary is tensored with the unit spin singlet. Precision cost is measured in \(p\), not in \(\log p\). For a fixed finite charge class \(2\le Z\le Z_{\max}\), a finite maximum gives one constant and the same exponent. No uniform bound for unbounded charge or variable electron number is claimed.

The detailed rational algorithm and operation count are [THEOREM_T_COMPOSITION.md](rwa_proof/THEOREM_T_COMPOSITION.md), checked separately in [THEOREM_T_AUDIT.md](rwa_proof/THEOREM_T_AUDIT.md). Its only conditional analytic premise, global graph RATE with exponent \(1/16\), is exactly (7), now proved.

Here are explicit schedules and their cost. Let \(N=n+2\), \(z=1+\lceil\log_2(Z+1)\rceil\). Safe bounds for the scaled exact moment coefficients and Gram conditioning are
\[
H_Z(n)=2^{40}(z+1)^2N^3,\qquad
h_n=2^{46}(z+1)^2N^{11}.
\]
With \(m_n\le N^4\), rational Gram positivity gives \(\|c\|_2^2\le2^{h_n}\) for every reduced-normalized real coefficient vector. This includes the existential analytic witness; no procedure for computing its unknown coefficients is assumed.

At stage \(n=1,2,\ldots\), set
\[
\tau_{n,p}=2^{-h_n-n-10},\qquad
\delta_{n,p}=2^{-n-10}.
\tag{9}
\]
These schedules are independent of \(p\); the requested precision enters the stopping test. Put \(s_0=-Z^2-1\), \(D=Q-2s_0A+s_0^2G\), and minimize the corrected fixed-shift quotient
\[
\frac{c^T(D+\tau_{n,p}I)c}{c^TGc}
\]
to additive error \(\delta_{n,p}\). This is a positive-definite rationally approximated generalized eigenproblem, not a minimization of global Rayleigh variance.

For an explicit entry-precision schedule, define
\[
B_0=(1+2Z)^2+2,\qquad K_0=2+2|s_0|+s_0^2,
\]
and choose
\[
s_{n,p}=\left\lceil\log_2
\frac{2^{20}B_0^2m_n^2K_0}{\tau_{n,p}\delta_{n,p}}\right\rceil+2.
\tag{10}
\]
Round the moments to a common dyadic denominator with enough guard bits to ensure absolute entry error at most the reciprocal expression in (10). Thus \(s_{n,p}=O_Z(n^{11})\). Exact rational PSD tests and retained negative witnesses solve the approximate pencil, with perturbation allowances for the interval matrices. They do not require deciding the exact sign of a transcendental expression.

The moment recurrences lie in the fixed rational linear span \(\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\); \(G\) and \(A\) are rational. All universal constants are evaluated by rational atanh and alternating-arctangent series with explicit remainders and outward dyadic rounding. The output vector is rational. Its mean is evaluated exactly; its second moment and variance are enclosed rationally. The known constants
\[
L_Z=-Z^2,\quad U_Z=-Z^2+5Z/8,\quad
\beta_Z=-5Z^2/8,\quad g_Z=Z(3Z-5)/8>0
\]
give the continuum separator. On stages with \(m\le U_Z\), the returned Temple interval is the outward rounding of
\[
\left[m-\frac{v_+}{\beta_Z-m},\ m\right].
\]
The algorithm stops when its rational width is at most \(2^{-p}\). Every emitted interval is valid independently of the convergence-rate proof.

The effective exponents are explicitly bounded by
\[
a=16\quad\text{(generation)},\qquad b=4\quad\text{(dimension)},\qquad
q=11\quad\text{(coefficient/size bound)},\qquad r=12\quad\text{(entry evaluation)}.
\]
The resulting per-stage exponent is
\[
B_* =\max\{16,\ 2\cdot4+12\cdot11,\ 5\cdot4+3\cdot11\}=140.
\]
The graph RATE and the fixed-shift spectral estimate imply a sufficient stopping order
\[
n(p)\le C'_Z(p+1)^{16}.
\]
Summing all stages gives \(16(140+1)=2256\) in (8). Formula (17) of the composition proof gives a sufficient order explicitly in terms of the RATE constants, \(g_Z\), and \(\mu_Z=U_Z-E_Z>0\). This last strict margin was already proved; it only determines a finite initial order before the mean filter succeeds.

The constants \(C_Z,C'_Z\) are traced through the analytic estimates and operation counts, but no useful numerical value for them is claimed. The adaptive algorithm uses none of these unknown analytic constants or prior energy digits as inputs. A gigantic conservative polynomial is still a complexity theorem; it is not a practical performance guarantee.

## 9. Scope and proof ledger

This reaches stopping condition A by new paper proofs. The primary RWA target is proved, its exact-dictionary local consequence is proved, one global admissible witness and its exterior are controlled, and all premises of the corrected energy algorithm are discharged. The older fixed-exponent obstruction and global-variance counterexample are unchanged. The older reports remain preserved byte for byte; [manifest.json](rwa_proof/manifest.json) records that check and hashes the new artifacts.

**PROVEN (Lean):** no new theorem, build, or axiom audit this session. **PROVEN (paper):** the analytic, approximation, and bit-cost results above. **EMPIRICAL:** no new rate data used. **CONJECTURED:** no conjecture is used as a premise of Theorem T. Machine-verified continuum mathematics, arbitrary molecules, more than two electrons, and general many-body tractability remain outside this result. The theorem certifies ground energy, not a closed-form wavefunction or arbitrary-observable algorithm.

RWA STATUS: PROVEN

LEADING-SINGULARITY STATUS: PROVEN

PAIR-COLLISION STATUS: PROVEN

REGULAR-REMAINDER LOCAL RATE STATUS: PROVEN

EXTERIOR PHYSICAL TAIL STATUS: PROVEN

ADMISSIBLE GLOBAL-WITNESS STATUS: PROVEN

GLOBAL GRAPH RATE STATUS: PROVEN

EFFECTIVE-DICTIONARY STATUS: PROVEN

THEOREM T STATUS: PROVEN

**THEOREM T DEPENDENCY AUDIT:**

1. **Actual operator, domain, ground-state existence, simplicity, symmetry, and separator.** [TWO_ELECTRON_THEOREM.md, §2](TWO_ELECTRON_THEOREM.md), with the preserved physical regularity audit. Sliced Hardy, Kato–Rellich, the hydrogenic spectrum and rank-one comparison give the displayed continuum hypotheses. No finite-basis substitution occurs.
2. **Physical vertex amplitude and extraction.** The verified Fournais et al. factorization, instantiated in [PHYSICAL_REGULARITY_AUDIT.md](dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md), supplies the actual leading term and Lipschitz amplitude. It does not supply all-order estimates by itself.
3. **Scale-uniform factorial regularity and closed-boundary descent.** [UNIFORM_ANALYTIC_AUDIT.md](rwa_proof/UNIFORM_ANALYTIC_AUDIT.md), [RWA_THEOREM.md](rwa_proof/RWA_THEOREM.md), and the exact Grušin/Fournais sources identified above. Oscillator estimates, common finite initialization and the verified factorial induction supply the missing uniformity; quantitative KS and invariant-series descent cover every shell stratum.
4. **Local dictionary realization.** [DYADIC_REMAINDER_ATTEMPT.md](rwa_proof/DYADIC_REMAINDER_ATTEMPT.md), its [independent audit](rwa_proof/DYADIC_REMAINDER_AUDIT.md), and the preserved [LEADING_SINGULARITY_THEOREM.md](dyadic_proof/LEADING_SINGULARITY_THEOREM.md). These prove the requested local composition; the global proof also uses the stronger direct vertex estimate from item 3.
5. **Uniform exterior analytic control and the true physical tail.** [EXTERIOR_ANALYTIC_ATTEMPT.md](rwa_proof/EXTERIOR_ANALYTIC_ATTEMPT.md), its [independent audit](rwa_proof/EXTERIOR_ANALYTIC_AUDIT.md), and the preserved [EXTERIOR_CONSTANTS.md](dyadic_proof/EXTERIOR_CONSTANTS.md). These control the actual state at large radius, including distant pair collisions.
6. **One admissible global vector, its polynomial tails, and normalized graph RATE.** [GLOBAL_DYADIC_ATTEMPT.md](rwa_proof/GLOBAL_DYADIC_ATTEMPT.md) and [GLOBAL_DYADIC_AUDIT.md](rwa_proof/GLOBAL_DYADIC_AUDIT.md). The exact telescoping identity, polynomial shell approximation, Poisson tails, physical norm conversion and localized Hardy prove (6)–(7) without changing the dictionary.
7. **Effective moments, rational Gram positivity, coefficient heights, and bit cost.** The preserved [RATE_DICTIONARY_DECISION.md](RATE_DICTIONARY_DECISION.md), [helium/THEORY.md](helium/THEORY.md) and its exact recurrences, sharpened to explicit all-order counts in [THEOREM_T_COMPOSITION.md](rwa_proof/THEOREM_T_COMPOSITION.md), §§1–3. No computable-witness assumption is added to the approximation theorem.
8. **Ground-branch selection, finite solve, interval rounding, and stopping.** The fixed-shift and continuum Temple proofs in [TWO_ELECTRON_THEOREM.md](TWO_ELECTRON_THEOREM.md), composed with the fully rational algorithm and schedules in [THEOREM_T_COMPOSITION.md](rwa_proof/THEOREM_T_COMPOSITION.md), §§4–5, and [THEOREM_T_AUDIT.md](rwa_proof/THEOREM_T_AUDIT.md). Every moment uncertainty is included, and (7) supplies the proved polynomial stopping order.
