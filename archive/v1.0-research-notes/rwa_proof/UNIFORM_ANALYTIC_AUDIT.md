> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Uniform analytic estimates for the scaled isolated-pair KS operator

Status: **PROVEN (paper proof)** for the operator lemma below. This is not a
Lean verification. The lemma does not by itself prove the subsequent descent
to distance coordinates, nor an approximation theorem for the dyadic dictionary.

The important quantitative point is that the analytic estimate is uniform in
the collision scale. Qualitative analyticity for each positive scale would not
be sufficient.

## 1. Operator and exact normalization

Let \(y\in\mathbb R^4\), \(t\in\mathbb R^3\), and let \(K:\mathbb R^4\to
\mathbb R^3\) be the usual quadratic Kustaanheimo--Stiefel map, normalized by
\(|K(y)|=|y|^2\) and
\[
 \Delta_y(F\circ K)=4|y|^2(\Delta_X F)\circ K.
\]
On an isolated electron--nucleus chart, scale \(x_1=\varepsilon X\),
\(x_2=\varepsilon t\). The Schrödinger equation, multiplied by
\(8|y|^2\) after \(X=K(y)\), is exactly
\[
 Q_\varepsilon u_\varepsilon=0,
 \qquad Q_\varepsilon=-\Delta_y-4|y|^2\Delta_t+B_\varepsilon,
\]
\[
 B_\varepsilon=-8\varepsilon Z
   +8\varepsilon |y|^2W(K(y),t)
   -8\varepsilon^2 E_Z|y|^2,
 \qquad W(X,t)=-Z/|t|+1/|X-t|.
\]
Choose fixed nested cylinders whose closure satisfies
\(|t|\ge d\) and \(|K(y)-t|\ge d\), for a fixed \(d>0\).
Every derivative of \(B_\varepsilon/\varepsilon\) then has a common
analytic bound, independently of \(0<\varepsilon\le\varepsilon_0\).
For example, this follows by taking a sufficiently small fixed complex
neighborhood on which the nonvanishing quadratic expressions under both
square roots avoid zero, and applying Cauchy's inequalities there. The
neighborhood size depends on \(d\), the fixed cylinder, and \(Z\), not on
\(\varepsilon\). The energy \(E_Z\) is one fixed finite real number.

For the electron--electron chart use \(X=x_1-x_2\) and
\(t=(x_1+x_2)/2\). Before scaling its kinetic operator is
\(-\Delta_X-\tfrac14\Delta_t\). The lifted operator is instead
\[
 -\Delta_y-|y|^2\Delta_t+4\varepsilon
 +4\varepsilon |y|^2
 \left[-Z/|t+K(y)/2|-Z/|t-K(y)/2|\right]
 -4\varepsilon^2 E_Z|y|^2.
\]
Thus it is covered by the same lemma with \(c=1\), whereas the nuclear
chart has \(c=4\). The spectator distances in this chart must also be
bounded below on the fixed cylinder.

## 2. Precise uniform operator lemma

Fix \(c>0\), a cylinder \(\Omega_0\subset\mathbb R^4_y\times
\mathbb R^3_t\), and a smaller concentric cylinder
\(\Omega_*\Subset\Omega_0\), both intersecting \(y=0\).
Write
\[
 P_c=-\Delta_y-c|y|^2\Delta_t,
 \qquad Q_\varepsilon=P_c+B_\varepsilon.
\]
Suppose \(B_\varepsilon\) extends analytically to a common neighborhood
of \(\overline\Omega_0\), and that there are \(M,A\ge1\) with
\[
 \sup_{\Omega_0}|D^\eta B_\varepsilon|
 \le \varepsilon M A^{|\eta|}|\eta|!
 \quad(0\le\varepsilon\le\varepsilon_0,
       \eta\in\mathbb N_0^7).
\]
There is a choice of sufficiently small \(\varepsilon_0>0\), and
constants \(C_*,A_*>0\), depending only on these fixed data and the
cylinder separation, such that the following holds. If
\(Q_\varepsilon v_\varepsilon=f_\varepsilon\) distributionally,
\[
 \|v_\varepsilon\|_{L^2(\Omega_0)}\le F,
 \qquad
 \sup_{\Omega_0}|D^\eta f_\varepsilon|
 \le F A^{|\eta|}|\eta|!,
\]
then, after decreasing the fixed interior cylinder if necessary,
\[
 \sup_{\Omega_*}|D^\eta v_\varepsilon|
 \le C_* F A_*^{|\eta|}|\eta|! .                 \tag{U1}
\]
The same constants work for every \(\varepsilon\). In particular,
the estimate is linear in \(F\). No assertion is made that these
constants are numerically optimal.

## 3. Common compact-support maximal estimate

The fixed model estimate can be checked directly. Fourier transform in
\(t\), with frequency \(\xi\). The fiber operator is
\[
 A_\xi=-\Delta_y+c|\xi|^2|y|^2.
\]
The four-dimensional harmonic oscillator satisfies
\(A_\xi\ge4\sqrt c\,|\xi|\). One proof is to expand the four
nonnegative norms
\(\|(\partial_{y_i}+\sqrt c|\xi|y_i)v\|_2^2\) and sum.
Consequently
\[
 \||D_t|v\|_2\le\frac1{4\sqrt c}\|P_cv\|_2.       \tag{U2}
\]
Here and below the Fourier normalization is chosen so that the symbol
of \(-\Delta_t\) is \(|\xi|^2\).

Integration by parts gives, in four \(y\) dimensions,
\[
 \mathop{\rm Re}\langle-\Delta_yv,|y|^2v\rangle
 =\||y|\nabla_yv\|_2^2-4\|v\|_2^2.
\]
It follows from (U2), fiberwise and then by Plancherel, that
\[
 \|\Delta_yv\|_2^2+
 \|c|y|^2\Delta_tv\|_2^2
 \le\frac32\|P_cv\|_2^2,                         \tag{U3}
\]
\[
 2c\sum_{i,j}\||y|\partial_{t_i}\partial_{y_j}v\|_2^2
 \le\frac32\|P_cv\|_2^2.                         \tag{U4}
\]
The full Hessian in either Euclidean variable has the same \(L^2\)
norm as its Laplacian, with the other variables held fixed. Individual
weighted monomials are bounded by \(|y|\) or \(|y|^2\).
On a fixed cylinder, (U2)--(U4) therefore control all top terms of
Grušin's norm (5.5), with \(m=2\), \(\delta=1\):
\[
 \mathcal M=\{(\alpha,\beta,\gamma):
 |\alpha|+|\beta|\le2,
 \ 2\ge|\gamma|\ge|\alpha|+2|\beta|-2\},
\]
\[
 N(v)=\sum_{\mathcal M}
       \|y^\gamma D_t^\beta D_y^\alpha v\|_2.
\]
The remaining terms have lower differential order. For compactly
supported \(v\), Poincaré in a fixed containing \(y\)-box and
\(\langle P_cv,v\rangle\ge\|\nabla_yv\|_2^2\) imply
\[
 \|v\|_2\le C_P\|P_cv\|_2,
 \qquad \|\nabla_yv\|_2\le\sqrt{C_P}\|P_cv\|_2.
\]
All harmless bounded powers of \(y\) can be included in a single
constant \(C_0\), so
\[
 N(v)\le C_0\|P_cv\|_2,
 \qquad v\in C_c^\infty(\Omega_0).               \tag{U5}
\]
If \(\varepsilon_0 MC_P\le1/2\), then
\[
 \|P_cv\|_2\le\|Q_\varepsilon v\|_2+
                  \varepsilon MC_P\|P_cv\|_2
 \le\|Q_\varepsilon v\|_2+\tfrac12\|P_cv\|_2.
\]
Thus
\[
 N(v)\le2C_0\|Q_\varepsilon v\|_2               \tag{U6}
\]
is exactly a common version of Grušin (5.5). The smallness requirement
is one fixed upper bound on the collision scale. It is not a
derivative-order restriction.

## 4. Uniform finite-order initialization; no qualitative shortcut

Grušin's factorial induction starts with finitely many derivative
norms. Their uniformity is not an automatic consequence of the
qualitative theorem. Here is the missing initialization argument.

Take three fixed nested cylinders. If
\(Q_\varepsilon w=g\), testing against \(\chi^2\overline w\),
taking the real part, and absorbing the cross terms gives the
Caccioppoli bound
\[
 \|\nabla_yw\|_{L^2(\Omega_1)}+
 \||y|\nabla_tw\|_{L^2(\Omega_1)}
 \le C\bigl(\|w\|_{L^2(\Omega_0)}+
             \|g\|_{L^2(\Omega_0)}\bigr).        \tag{U7}
\]
The constant depends on fixed cutoff derivatives, \(c\), and a common
bound on \(|B_\varepsilon|\). Young's inequality bounds the
\(\langle g,\chi^2w\rangle\) term by the squares of the two norms
on the right. The cutoff errors are bounded because \(y\) is bounded
on the cylinder. Formula (U7) holds equally for complex \(w\).

The commutator is explicit:
\[
 [P_c,\chi]w=-2\nabla_y\chi\cdot\nabla_yw
 -(\Delta_y\chi)w
 -2c|y|^2\nabla_t\chi\cdot\nabla_tw
 -c|y|^2(\Delta_t\chi)w.
\]
It is \(L^2\)-controlled by (U7) on the intermediate cylinder.
Apply (U6) to \(\chi w\) to obtain
\[
 \|w\|_{H^1(\Omega_2)}+
 \|D_y^2w\|_{L^2(\Omega_2)}
 \le C\bigl(\|w\|_{L^2(\Omega_0)}+
             \|g\|_{L^2(\Omega_0)}\bigr).        \tag{U8}
\]
For smooth \(w\) this is a direct calculation. Distributional
solutions with analytic right side are smooth by Grušin Theorem 5.1
(or its preceding hypoellipticity statement), whose hypotheses hold
for every member of this family. This qualitative use only permits
the differentiations; it supplies none of the uniform constants.

Tangential differentiation commutes with \(P_c\). In particular,
\[
 Q_\varepsilon D_t^\beta v
 =D_t^\beta f-
  \sum_{0<\eta\le\beta}\binom\beta\eta
     (D_t^\eta B_\varepsilon)D_t^{\beta-\eta}v.    \tag{U9}
\]
Starting from the assumed \(L^2\) bound, repeated application of
(U8) on finitely many fixed nested cylinders proves uniform bounds
for every prescribed finite number of tangential derivatives,
together with their first and second \(y\) derivatives. At stage
\(|\beta|\), the \(L^2\) norm of \(D_t^\beta v\) was supplied
by the preceding stage; all terms on the right of (U9) have already
controlled lower tangential derivatives. Coefficient derivatives of
each required finite order have common bounds.

Finally use the ordinary constant-coefficient interior elliptic
estimate in \(y\), with \(L^2_t\) as coefficient Hilbert space,
on
\[
 -\Delta_yv=c|y|^2\Delta_tv-B_\varepsilon v+f.   \tag{U10}
\]
For completeness, this interior estimate follows by multiplying by
a fixed \(y\) cutoff and using
\(\|D_y^2h\|_2=\|\Delta_yh\|_2\), then induction on
the number of \(y\) derivatives; cutoff commutators have lower
\(y\) order. Every pair of additional \(y\) derivatives can cost
two additional tangential derivatives through (U10). Thus, for any
fixed integer \(q\), first carrying out sufficiently many of the
tangential steps gives a full \(H^q\) estimate on a fixed smaller
cylinder. In particular take \(q=12\). There is a constant \(C_{12}\),
independent of \(\varepsilon\), such that
\[
 \|v_\varepsilon\|_{H^{12}(\Omega_3)}
 \le C_{12}F.                                   \tag{U11}
\]
Only finitely many coefficient and source derivatives and finitely
many fixed cutoffs enter \(C_{12}\). Choosing all these cutoffs
beforehand, for example with equal gaps between consecutive
cylinders, makes their independence of \(\varepsilon\) explicit.
The exponent 12 is a safe fixed initialization order; it is not a
Gevrey loss or an estimate on the ultimate derivative order.

## 5. Factorial induction from the verified primary theorem

Primary source: V. V. Grušin, *On a class of elliptic
pseudodifferential operators degenerate on a submanifold*,
Mathematics of the USSR--Sbornik **13** (1971), 155--185,
DOI [10.1070/SM1971v013n02ABEH001033](https://doi.org/10.1070/SM1971v013n02ABEH001033).
The accessible primary English PDF is archived locally at
`rwa_proof/sources/grushin1971.pdf`; the relevant printed pages are
179--183, Theorem 5.1, Lemmas 5.1--5.3, Proposition 5.1, equations
(5.5), (5.14), and (5.20)--(5.24).

The operator belongs to the class (5.1), with \(m=2\), \(\delta=1\),
four degenerate \(y\) coordinates and three tangential coordinates.
Its top symbol is elliptic for \(y\ne0\). For a unit nonzero
tangential frequency the model operator is the positive harmonic
oscillator \(-\Delta_y+c|y|^2\), so its Schwartz kernel is zero.
These check Conditions 1 and 2 used in Theorem 5.1. The potential
terms are lower-order terms of the permitted class.

More importantly, Proposition 5.1 is a quantitative induction from
the compact-support estimate (5.5) and the factorial coefficient and
source estimates (5.14). The proof uses only:

1. the constant in (5.5);
2. the common analytic coefficient and source constants in (5.14);
3. fixed cutoff dimensions and derivative bounds;
4. finitely many initial weighted derivative norms, with threshold
   \(r_0=m(3+\delta)=8\).

The initial weighted norms involve derivatives through a fixed
finite order (at most ten with this choice); (U11) bounds them.
Apply the proposition to \(v_\varepsilon/F\) when \(F>0\).
All four inputs now have common constants. Consequently its
recurrence (5.21)--(5.23) has one common choice of its constant \(B\),
and (5.20) yields common bounds of the form \((C\ell)^\ell\).
The fixed Sobolev embedding and Stirling step (5.24) yield (U1),
with constants independent of \(\varepsilon\). If \(F=0\), the
assumed \(L^2\) bound already gives \(v=0\).

This is a direct uniform instantiation of the source's induction;
it does not infer uniformity from the mere assertion of real
analyticity. The finite-order initialization is supplied above,
rather than silently folded into a scale-dependent constant.

## 6. Consequence for the scaled physical difference

Suppose the lifted physical solution is distributional, as required
in the usual KS argument, and the physical wavefunction is
Lipschitz in a fixed neighborhood of the triple collision. Set
\(a_0=\psi_Z(0)\), and
\[
 v_\varepsilon=(u_\varepsilon-a_0)/\varepsilon.
\]
On the fixed scaled cylinder its \(L^2\) norm is bounded
independently of \(\varepsilon\): the physical arguments have norm
at most a fixed multiple of \(\varepsilon\). Its equation is
\[
 Q_\varepsilon v_\varepsilon
   =-a_0B_\varepsilon/\varepsilon.
\]
The right side has a uniform analytic norm by Section 1. Therefore
(U1) gives
\[
 \sup_{\Omega_*}
 |D_y^\alpha D_t^\beta(u_\varepsilon-a_0)|
 \le C\varepsilon A^{|\alpha|+|\beta|}
                 (|\alpha|+|\beta|)! .          \tag{U12}
\]
This is the exact uniform pair-chart estimate needed before KS
descent. The remaining descent and compatibility arguments must
preserve a common analytic radius and exponential coefficient
bounds. Neither follows just by writing \(|X|=|y|^2\); that
algebraic/analytic step is a separate part of the proof.

## 7. Audit boundary

The constants proved uniform here depend on the fixed normalized
chart, spectator separation, \(Z\), and \(E_Z\). A finite cover of a
compact normalized shell can take their maximum. This lemma does
not apply to a chart on which another spectator separation tends to
zero. Such overlaps have to be assigned to the appropriate single
pair chart on the normalized shell, where distinct collision sets
are separated.

No floating-point computation, formal Fock expansion, numerical
convergence experiment, or assertion of \(C^{1,1}\)-to-analytic
regularity was used. The known Lipschitz bound is used solely to
bound the amplitude of \(u_\varepsilon-a_0\); all higher derivative
bounds come from the operator estimates and factorial induction.

## 8. Independent audit of the reduced equation and RWA composition

The accompanying REMAINDER_EQUATION.md was independently checked after
the operator lemma above was completed. The scalar operator identities
below passed that check. A subsequent exact polynomial audit caught a
coordinate-expansion typo that this first review missed: the correct
formula is \(q=c(S-c)-ab\), not \(cS-ab\). The displayed physical
definition \(q=(r^2+s^2-u^2)/2\) and the operator identities were correct.
The corrected file now passes all 26 identities in
`audit_reduced_identities.py`. In particular:

- The reduced measure is \(16\pi^2rsu\,da\,db\,dc\), since the
  distance measure is \(8\pi^2rsu\,dr\,ds\,du\) and the linear
  coordinate Jacobian has absolute determinant two.
- With the notation of that file,
  \(\det G=\mathsf A+\mathsf B-\mathsf A^2-\mathsf B^2\), which
  expands to its displayed rational determinant.
- \(v^TGv=2Z^2+1/2-2Z\Theta\), so
  \(W=-Z^2-1/4+Z\Theta-E\).
- For \(J=q\log T\), the source signs follow from
  \(\mathcal LJ=16q/T\),
  \(\mathbf t\cdot\nabla q=-ZqS/(rs)-u/2\), and
  \(\mathbf t\cdot\nabla\log T=2f/T\). Thus
  \(-\mathcal PJ=(8+2f)q/T+
  [-ZqS/(rs)-u/2-Wq]\log T\).
- After multiplication of the scaled equation by
  \(\varepsilon^2\), these terms have respectively the powers
  \(\varepsilon^2,\varepsilon^3,\varepsilon^3,\varepsilon^4\)
  appearing in (PDE11). The constant-subtracted Cartesian equation
  has right side \((-V+\varepsilon E)\psi_0\), as stated.
- The three open faces are collinear configurations; the three
  positive axes are the isolated pair collisions. No pair collision
  is confused with a generic collinear face.

The completed RWA_THEOREM.md was then audited independently.
Its quantitative descent and final estimate pass the following checks.

First, the KS lift is the actual pullback of a physical function, so
the fiber-invariance assumption behind Proposition 4.4 is satisfied.
The all-order derivative estimate divided by multi-index factorials
gives a geometric Taylor coefficient bound, since in seven variables
\(|\eta|!/\eta!\le7^{|\eta|}\). The source's coefficient descent
therefore has common radii and common analytic norms.

Second, uniqueness of the analytic-plus-distance decomposition is
valid. Restriction to \(X=tv\) and analytic continuation in \(t\)
changes the sign of \(t\) but not of \(|t|\); comparison forces both
analytic components to vanish. Hence their separate rotational
invariance follows from that of the physical function.

Third, for an \(SO(2)\)-invariant analytic function,
the coefficient of \(w^mz^j(s-s_0)^\ell\), where
\(w=x^2+y^2\), equals the coefficient of
\(x^{2m}z^j(s-s_0)^\ell\) after setting \(y=0\).
A Cartesian polydisc bound \(M\) at radius \(h\) therefore gives
the exact bound \(Mh^{-2m-j-\ell}\), with geometric summation
bounded by \(8M\) on the smaller polydisc. This is an exponential
coefficient conversion, not a hidden factorial loss.

The nuclear substitutions
\[
 z=(r^2+s^2-u^2)/(2s),\qquad w=r^2-z^2
\]
are holomorphic on fixed neighborhoods of \(r=0,s=u=s_0>0\).
For the electron--electron chart the corresponding formulas are
\[
 \tau=\sqrt{(r^2+s^2)/2-u^2/4},\qquad
 z=(r^2-s^2)/(2\tau),\qquad w=u^2-z^2.
\]
Their denominators and the positive square-root branch stay
uniformly separated from zero near \(u=0,r=s>0\).
The same \(SO(2)\) argument covers noncollision collinear points;
the remaining compact noncollinear set admits analytic planar
representatives with a uniformly nonzero transverse coordinate.

For the compact-cover step, choose smaller chart cores that already
cover the normalized shell and retain their larger holomorphic
neighborhoods. Take a finite subcover of those cores. A fixed
positive distance from each core to its larger neighborhood's
boundary then supplies the common complex radius. This is the
precise version of the finite-cover minimum-radius argument; an
arbitrary later shrinking of a cover would not suffice.

Finally, the extracted logarithm on a normalized complex shell has
norm \(O(\varepsilon^2(1+|\log\varepsilon|))=O(\varepsilon)\).
The cusp conjugation contributes \(O(\varepsilon)\) as well.
Cauchy's inequality with a common radius therefore yields
\[
 |\partial^\nu(\widehat{\mathcal R}_Z-\psi_0)|
 \le C A^{|\nu|}\nu!\,S^{1-|\nu|}.
\]
Taking \(S\le1\) and \(\nu!\le|\nu|!\) proves the requested
weight \(S^{1/2-|\nu|}\). The scale is held fixed while differentiating
the local extension, so no derivative of the chosen
\(\varepsilon=S(x)\) is erroneously introduced.

This audit finds no remaining regularity gap in the RWA composition.
It says nothing by itself about constructing one admissible member
of the specified dyadic dictionary.
