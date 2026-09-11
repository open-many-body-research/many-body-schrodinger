> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A direct quantitative factorial recurrence for the KS model

Evidence category: **paper proof**, with an auxiliary finite integer check.
This is not a Lean theorem, a proved physical eigenfunction statement, or a
certificate for a continuum energy. This version is new work; the frozen
Grušin instantiation and the sealed H12 lemma are unchanged.

The result proves the exact all-order implication needed after weak H12
initialization. It derives both localization commutators and the derivative
commutator directly for the actual operator. It also removes the collision
scale smallness restriction at this operator-lemma stage. The still separate
physical inputs and KS descent are listed in Section 9.

## 1. Exact statement and constants

Write (y\in\mathbb R^4), (t\in\mathbb R^3), fix (a,b,c>0),

\[
 0<\rho\le\min(1,a/2,b/2),\qquad
 \Omega_s=(-a+s,a-s)^4\times(t_0+(-b+s,b-s)^3),\quad 0\le s\le\rho.
\]

Let (P_c=-\Delta_y-c|y|^2\Delta_t), (Q=P_c+B). Suppose that

* (B\in C^\infty(\Omega_0)) and
  (\|D^\eta B\|_\infty\le M A^{|\eta|}|\eta|!), with (M,A\ge1);
* (f\in C^\infty(\Omega_0)) and
  (\|D^\eta f\|_{L^2(\Omega_0)}\le F A^{|\eta|}|\eta|!), with (F\ge0);
* (v\in H^{12}(\Omega_0)), (\|v\|_{H^{12}(\Omega_0)}\le H), and
  (Qv=f) as an equality of distributions, with (H\ge0).

Complex (B,f,v) are allowed. There is no smallness assumption on (M).
H12 can be supplied from an outer L2 box by the sealed weak initialization
lemma; it does not presuppose the following all-order bounds.

Here are explicit, deliberately coarse constants. All are independent of the
derivative order and of any parameter shared by this family of hypotheses:

\[
\begin{split}
 R&=2a,\quad W=\max(1,R^2),\quad C_P=4a^2,\quad \kappa=a-\rho,\\
 C_{\max}&=\max\left(WC_P,\,2aW,\,{W\over4\sqrt c},\,
 W\sqrt{3/2},\,\max(1,R)\sqrt{3/(4c)},\,{\sqrt{3/2}\over c}\right),\\
 C_0&=498 C_{\max},\quad
 C_{\rm cut}=108\max(1,\kappa^{-2})+81c,\\
 C_{\rm com}&=M+6c,\quad
 C=\max\{1,C_0\max(1,C_{\rm cut}+M,C_{\rm com})\},\\
 B_0&=2CA,\quad S=F+498WH,\\
 L_y&=2(a-\rho),\quad L_t=2(b-\rho),\\
 E_{\rm box}&=(L_y^{-1/2}+L_y^{1/2})^4
                 (L_t^{-1/2}+L_t^{1/2})^3,\\
 C_*&=2B_0 E_{\rm box}(2B_0/\rho)^{11}3^{12}12^{11},\qquad
 A_*=(2B_0/\rho)\,6144.
\end{split}                                                    \tag{R1}
\]

The conclusion is

\[
 \sup_{\Omega_\rho}|D^\eta v|
       \le C_* S A_*^{|\eta|}|\eta|! .                          \tag{R2}
\]

The smooth representative in (R2) is supplied by the equation. In particular,
if (F,H) are both bounded by a common physical amplitude times fixed
constants, (R2) is linear in that amplitude. The factorial bound implies real
analyticity, with a common local power-series radius: Taylor's integral
remainder on a segment has size at most

\[
 C_*S\bigl(A_*\|z-z_0\|_1\bigr)^{k+1}
\]

at truncation order (k). Thus the series converges to (v) whenever the
segment is inside the box and (A_*\|z-z_0\|_1<1). The same series gives a
holomorphic extension near each interior real point. At a complex point in
the extension its bound is explicitly

\[
 {C_*S\over 1-A_*\|z-z_0\|_1},
\]

so the half-radius neighborhood has bound (2C_*S). Identification with
the real solution uses the retained real-box margin. No statement about
global gluing or descent is silently included.

## 2. The full weighted norm and its compact-support estimate

Use exactly the source's specialized set of triples, not merely its principal
terms:

\[
 \mathcal M=\{(\alpha,\beta,\gamma):
   |\alpha|+|\beta|\le2,\quad
   2\ge|\gamma|\ge|\alpha|+2|\beta|-2\},
\]
\[
 N(w;U)=\sum_{\mathcal M}
       \|y^\gamma D_y^\alpha D_t^\beta w\|_{L^2(U)}.
                                                                  \tag{R3}
\]

There are exactly 498 triples. Grouping by ((|\alpha|,|\beta|)), their
counts are (15,60,45,150,168,60) for

\[
 (0,0),(1,0),(0,1),(2,0),(1,1),(0,2),
\]

respectively. In particular, unweighted first (t)-derivatives belong to
the norm. This fact matters for removing the smallness assumption below.

The oscillator inequalities proved in the frozen audit, and independently
checked in the H12 continuation, give for compactly supported (w)

\[
 \|D_t w\|_2\le(4\sqrt c)^{-1}\|P_cw\|_2,
\]
\[
 \|D_y^2w\|_2^2+\|c|y|^2\Delta_tw\|_2^2
       \le\tfrac32\|P_cw\|_2^2,
\]
\[
 \sum_{i,j}\||y|D_{y_i}D_{t_j}w\|_2^2
       \le {3\over4c}\|P_cw\|_2^2.                            \tag{R4}
\]

For the first line, the norm of (D_t) denotes the full Euclidean gradient;
for (D_y^2) it denotes the full Euclidean Hessian. In the second line it is
enough to bound each individual Hessian entry by the displayed quantity.
The first inequality follows by partial Fourier transformation from the
four-dimensional oscillator lower bound (4\sqrt c|\xi|). Integration by
parts of its cross term gives the constant (3/2); no spectral theorem for
the physical Hamiltonian is used here.

Poincare in one (y) interval and the energy identity imply

\[
 \|w\|_2\le C_P\|P_cw\|_2,
 \qquad \|D_yw\|_2\le\sqrt{C_P}\|P_cw\|_2.
\]

The elementary interval estimate used here is

\[
 \|w\|_2\le2a\|\partial_{y_1}w\|_2,
\]

valid for functions compactly supported in the containing interval of
length (2a). On the box, (|y|\le R). Bounds (R4), the two preceding
inequalities, and the six groups in (R3) now give

\[
 N(w;\mathbb R^7)\le C_0\|P_cw\|_2,
       \qquad w\in C_c^\infty(\Omega_0).                        \tag{R5}
\]

For mixed second derivatives use

\[
 |y^\gamma|\le\max(1,R)|y| \quad (1\le|\gamma|\le2),
\]

and for pure second (t)-derivatives use (|y^\gamma|\le |y|^2).
These explain all entries of (C_{\max}), including the dependence on (c).
The compact estimate also holds for compactly supported (H^2) functions,
by ordinary convolution and convergence of all the displayed terms.

## 3. Smoothness licenses; the all-order bound is not assumed

The H12 proof established a local weak gain: if (Qw=g) and (w,g\in L^2),
then on a smaller fixed box (w,D_tw,D_yw,D_y^2w\in L^2). Its proof uses
partial (t)-convolution, ordinary weak (y)-ellipticity and (R4); it does
not invoke qualitative analytic hypoellipticity.

That proof applies for any finite derivative target. For a fixed integer

\[
 q\ge2,
\]

first make (q) tangential gains, using the distributional identity

\[
 QD_t^\beta v=D_t^\beta f-
   \sum_{0<\eta\le\beta}\binom\beta\eta
       (D_t^\eta B)D_t^{\beta-\eta}v.
\]

Every right-hand (v) derivative has strictly smaller tangential order.
This supplies all derivatives with at most two (y)-derivatives and total
order at most (q). Subsequently use

\[
 -\Delta_yv=c|y|^2\Delta_tv-Bv+f
\]

for (\lceil(q-2)/2\rceil) weak elliptic gains. To create a target of

\[
 |\alpha'|=2j+1\text{ or }2j+2,
\]

differentiate the equation at a base index (alpha=\alpha'-\gamma),

\[
 \gamma\le\alpha',\quad |\gamma|=2.
\]

Then (|\alpha|=2j-1) or (2j), respectively. All terms from

\[
 D_y^\alpha(|y|^2\Delta_tD_t^\beta v)
\]

have at most (2j) (y)-derivatives and total order at most (q), and
are already known. This includes the odd-order targets. Only finitely many
source and coefficient derivatives, of order at most (q-1), enter. There
are (2q+2\lceil(q-2)/2\rceil) fixed gaps in this finite argument. For
each (q) they can be chosen in an arbitrary positive outer-to-inner
reserve; their constants are used solely to prove membership in (H^q).

Consequently (v\in C^\infty(\Omega_0)). No constants from these arbitrarily
high finite gains occur in (R1). Only the separately proved initial (H^{12})
norm is used in the uniform factorial recurrence that follows.

## 4. Exact derivative cost and initial norms

For integers (A_y,B_t\ge0), put

\[
 \omega(A_y,B_t)=A_y+B_t+\min(A_y,4),
 \qquad
 \mathcal R_r=\{(\alpha,\beta):\omega(|\alpha|,|\beta|)\le r\}.
                                                                  \tag{R6}
\]

This is exactly the union printed on Grušin p. 180 for (m=2,\delta=1):

\[
 \{|\alpha|\le4,\ 2|\alpha|+|\beta|\le r\}
 \ \cup\
 \{|\alpha|\ge4,\ |\alpha|+|\beta|\le r-4\}.
\]

Both formulas coincide when (|\alpha|=4). Define for every integer

\[
 r\ge0:\qquad N_r(s)=\max_{(\alpha,\beta)\in\mathcal R_r}
       N(D_y^\alpha D_t^\beta v;\Omega_s).                         \tag{R7}
\]

Removing a multi-index of total size (j) lowers (omega) by at least

\[
 j.                                                               \tag{R8}
\]

For (0\le r\le8), the total derivative order in every summand of (R7)
is at most (r+2\le10). Therefore

\[
 N_r(s)\le H_0:=498WH,
       \qquad 0\le r\le8,\quad 0\le s\le\rho.                    \tag{R9}
\]

The weighted norm adds up to two derivatives after the index pair, rather
than before it. The H12 initialization is more than sufficient.

## 5. Localization commutator with exact losses

Fix (e>0,s\ge0,s+e\le\rho). A product cutoff (phi) can be chosen
equal to one on (Omega_{s+e}), compactly supported in (Omega_s), with

\[
 |\partial_i\phi|\le3e^{-1},\qquad
 |\partial_i^2\phi|\le27e^{-2}.                                  \tag{R10}
\]

For example use the quintic (10u^3-15u^4+6u^5), extended by zero and one,
on the transition of width (3e/4) from each inner half-width to the
half-width larger by (3e/4). Its first two derivatives have bounds 2 and
15. The resulting cutoff is (C^2), which suffices by the H2 version of
(R5). It is one inside the inner box and zero at least (e/4) before the
outer boundary. On the support of a (y)-derivative of (phi),

\[
 |y|\ge a-s-e\ge\kappa>0.                                       \tag{R11}
\]

For (D=D_y^\alpha D_t^\beta), the commutator is exactly

\[
 [P_c,\phi]Dv=
 -2\nabla_y\phi\cdot\nabla_yDv-(\Delta_y\phi)Dv
 -2c|y|^2\nabla_t\phi\cdot\nabla_tDv-c|y|^2(\Delta_t\phi)Dv.
                                                                  \tag{R12}
\]

Let ((\alpha,\beta)\in\mathcal R_r), (r\ge9), and put

\[
 k=|\alpha|+|\beta|.
\]

For either first-order term, if (k\ge1), remove one derivative from (D)
and place it together with the displayed extra derivative in the outer norm

\[
 N(D^{\rm remainder}v;\Omega_s).
\]

The remaining index belongs to (mathcal R_{r-1}) by (R8). Every second
derivative with every weight (y_i^2) is in (mathcal M). For the first

\[
 y\text{-cutoff term use }
 |\partial_{y_i}Dv|\le\kappa^{-2}
      \sum_{\ell=1}^4|y_\ell^2\partial_{y_i}Dv|
\]

on (R11); for the first (t)-cutoff term the factor (|y|^2) is already
present. If (k=0), the displayed first derivative is itself in the outer
norm, with the necessary weight, and base index zero lies in

\[
 \mathcal R_{r-1}.
\]

For either second-order cutoff term remove two derivatives from (D) when

\[
 k\ge2,
\]

and put them in the outer norm, again using (R11) for the (y)-cutoff
term. The base index lies in (mathcal R_{r-2}). If (k<2), the whole
derivative (D) is an outer norm term; index zero is permitted. The fixed
threshold (r\ge9) leaves ample reserve for these cases.

Summing the four (y) and three (t) directions in (R12) gives

\[
 \|[P_c,\phi]Dv\|_2
 \le C_{\rm cut}\bigl(e^{-1}N_{r-1}(s)+e^{-2}N_{r-2}(s)\bigr).
                                                                  \tag{R13}
\]

More precisely the first coefficient is

\[
 24\max(1,\kappa^{-2})+18c,
\]

and the second is (108\max(1,\kappa^{-2})+81c=C_{\rm cut}).
Thus only first and second cutoff derivatives are used at every order;
there is no hidden derivative-order dependence in their constants.

## 6. Coefficient commutator and the undifferentiated potential

Since (t)-differentiation commutes with (P_c), the principal coefficient
commutator consists only of

\[
 2c\sum_{i=1}^4\alpha_i y_i\Delta_t
          D_y^{\alpha-e_i}D_t^\beta v,
 \qquad
 c\sum_{i=1}^4\alpha_i(\alpha_i-1)\Delta_t
          D_y^{\alpha-2e_i}D_t^\beta v,                           \tag{R14}
\]

up to their immaterial overall signs. To check exactly the new norm indices,
write (A_y=|\alpha|,B_t=|\beta|). For each (t) direction (j):

| Term | Case | Outer weighted derivative | Base total orders | Loss in (omega) |
|---|---|---|---|---|
| One derivative hits (|y|^2) | (A_y=1) | (y_iD_{t_j}) | ((0,B_t+1)) | 1 |
| One derivative hits (|y|^2) | (A_y\ge2) | (y_iD_{y_k}D_{t_j}) | ((A_y-2,B_t+1)) | at least 1 |
| Two derivatives hit (|y|^2) | (A_y=2,3) | (D_{t_j}) | ((A_y-2,B_t+1)) | 3 |
| Two derivatives hit (|y|^2) | (A_y\ge4) | an unweighted second (y) derivative | ((A_y-4,B_t+2)) | at least 2 |

In the second row choose (e_k\le\alpha-e_i). In the last row choose
any multi-index of size two below (alpha-2e_i). Thus every stated base
index exists componentwise, not just at the level of total degrees. Every
outer derivative in the table belongs to (mathcal M). It follows that

\[
 \|[P_c,D]v\|_{L^2(\Omega_s)}
 \le6crN_{r-1}(s)+3cr(r-1)N_{r-2}(s).                           \tag{R15}
\]

For the potential commutator, group the Leibniz terms by the total number

\[
 \nu=|\eta|\ge1
\]

of derivatives falling on (B). The sum of their multi-index binomial
coefficients is (inom{k}{\nu}). By (R8) all remaining indices belong
to (mathcal R_{r-\nu}); (k\le r) gives

\[
 \|[B,D]v\|_2
 \le M\sum_{\nu=1}^r A^\nu{r!\over(r-\nu)!}N_{r-\nu}(s).
\]

Together,

\[
 \|[Q,D]v\|_2
 \le C_{\rm com}\sum_{\nu=1}^r
       A^\nu{r!\over(r-\nu)!}N_{r-\nu}(s).                     \tag{R16}
\]

Finally, there is a useful separate index saving:

\[
 \|Dv\|_{L^2(\Omega_s)}\le N_{r-1}(s),\qquad r\ge9.            \tag{R17}
\]

When (k\ge1), remove one derivative from (D) and use that unweighted
first derivatives of both kinds belong to (mathcal M). When (k=0),
use the zero base index. Therefore

\[
 \|B\phi Dv\|_2\le M N_{r-1}(s).
\]

This estimate replaces absorption of the potential into (R5). It explains
why the factorial theorem requires a common bound on (B), but no bound
of the form (|B|_\infty C_P<1).

## 7. Closed recurrence and exact finite geometric sum

Since (phi=1) on the inner box, apply (R5) to (phi Dv) and use

\[
 P_c(\phi Dv)=\phi\bigl(Df+[Q,D]v-BDv\bigr)+[P_c,\phi]Dv.
\]

The source satisfies (|Df|_2\le FA^r r!). Bounds (R13), (R16),
(R17), (e\le\rho\le1), and the definition of (C) yield

\[
 N_r(s+e)\le C\left[
 FA^r r!+e^{-1}N_{r-1}(s)+e^{-2}N_{r-2}(s)
 +\sum_{j=1}^r A^j{r!\over(r-j)!}N_{r-j}(s)\right],\quad r\ge9.
                                                                  \tag{R18}
\]

If (S=0), then (H=0) and (v=0); suppose (S>0). Fix an integer

\[
 \ell\ge1,\quad h=\rho/\ell,\qquad
 d_r={h^r\over S}N_r((r+1)h),\quad 0\le r\le\ell-1.
                                                                  \tag{R19}
\]

For (r\le8), (d_r\le1) by (R9) and (h\le1). For (r\ge9),
apply (R18) with (s=rh,e=h). Its lower norms are taken on a box
contained in the box used in (d_{r-j}), because

\[
 (r-j+1)h\le rh.
\]

Also (h^j r!/(r-j)!\le(\rho r/\ell)^j\le1) and

\[
 h^r r!\le1.
\]

Hence

\[
 d_r\le C\left[A^r+d_{r-1}+d_{r-2}+
                 \sum_{j=1}^r A^j d_{r-j}\right]
 \le B_0^{r+1}+\sum_{j=1}^r B_0^j d_{r-j}.                     \tag{R20}
\]

Here (B_0=2CA\ge2): it bounds the source coefficient and, for (j=1,2),
the combined coefficients (C(1+A^j)\le B_0^j); for (j>2),

\[
 CA^j\le B_0^j.
\]

Induction with the **finite** geometric sum gives

\[
 d_r\le(2B_0)^{r+1}.                                            \tag{R21}
\]

Indeed the inductive upper bound for the right side of (R20) is exactly

\[
 B_0^{r+1}+\sum_{j=1}^r B_0^j(2B_0)^{r-j+1}
   =B_0^{r+1}(2^{r+1}-1)
   \le(2B_0)^{r+1}.                                             \tag{R22}
\]

This calculation does not require extending the sum to infinity. Choosing

\[
 \ell=r+1
\]

in (R19) proves for every (r\ge0)

\[
 N_r(\rho)\le2B_0S\left({2B_0(r+1)\over\rho}\right)^r.          \tag{R23}
\]

For (r\le8) the same bound follows directly from (R9). Thus the initial
H12 bound, the exact norm indices and the model maximal estimate give one
common factorial recurrence constant for the entire parameter family.

## 8. Pointwise derivatives without a hidden embedding constant

For an interval (I) of length (L) and (x\in I), integration of the
fundamental theorem of calculus gives

\[
 g(x)=L^{-1}\int_I g(s)\,ds+\int_I K_x(s)g'(s)\,ds,
       \qquad |K_x(s)|\le1.
\]

The two kernels have L2 norms at most (L^{-1/2}) and (L^{1/2}).
Tensoring this identity in all seven variables, applying Cauchy--Schwarz
to each term, and then taking the maximum gives

\[
 \sup_{\Omega_\rho}|w|
 \le E_{\rm box}\max_{\nu\in\{0,1\}^7}
                 \|D^\nu w\|_{L^2(\Omega_\rho)}.                \tag{R24}
\]

This is an H7 mixed-derivative embedding. It applies by density whenever
the indicated weak derivatives are L2. No derivative-order-dependent
constant is involved when (w=D^\eta v).

If (|\eta|=k), every derivative in (R24) has total order at most (k+7).
Its cost (R6) is at most (k+11), so (R23) gives

\[
 \sup|D^\eta v|
 \le2B_0SE_{\rm box}(2B_0/\rho)^{k+11}(k+12)^{k+11}.
\]

The elementary factorial estimate

\[
 (k+12)^{k+11}\le3^{12}12^{11}(3\,2^{11})^k k!,\quad k\ge0,
                                                                  \tag{R25}
\]

follows, for (k\ge1), from (k!\ge(k/e)^k\ge(k/3)^k),

\[
 (1+12/k)^k\le e^{12}\le3^{12},\qquad
 k+12\le12(k+1)\le12\,2^k.
\]

At (k=0) it is immediate. This proves (R2) with exactly (R1).

## 9. What this changes, and what remains open

For the actual scaled KS families take (c=4) on electron--nucleus charts
and (c=1) on electron--electron charts. A common bound

\[
 \|D^\eta(B_\varepsilon/\varepsilon)\|_\infty
       \le M_b A^{|\eta|}|\eta|!,\quad0<\varepsilon\le\varepsilon_0
\]

implies the hypothesis on (B) with (M=\max(1,\varepsilon_0M_b)).
For (v_\varepsilon=(u_\varepsilon-a_0)/\varepsilon), the source is

\[
 f_\varepsilon=-a_0B_\varepsilon/\varepsilon.
\]

Its required L2 analytic constant can be taken to be

\[
 F=|a_0|M_b|\Omega_0|^{1/2}.
\]

The sealed H12 lemma supplies a uniform (H) on this inner box from the
actual weak scaled equation, a common L-infinity/Lipschitz amplitude, and
finite coefficient/source bounds on an outer box. Then (R2) proves

\[
 \sup|D_y^\alpha D_t^\beta(u_\varepsilon-a_0)|
 \le\varepsilon C_*S A_*^{|\alpha|+|\beta|}
                    (|\alpha|+|\beta|)!.
\]

This discharges the all-order **operator recurrence** at paper level.
Unlike the frozen instantiation, its proof is self-contained after the
oscillator maximal estimate and weak initialization. The maximum allowed
scale need not be decreased merely to absorb the zeroth-order potential.

The physical weak KS pullback, the physical amplitude hypothesis, the
compatible distance-coordinate descent, coordinate-boundary configurations
and the chart cover remain explicit separate obligations. This result alone
does not establish G1, an H2 approximation of the physical eigenfunction,
the physical spectrum, formal correctness, an executable energy solver or
bit complexity. There is no claim of a new general analytic-hypoellipticity
theorem or of literature novelty.

## 10. Sources, preservation and finite checks

Frozen commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`.
Annotated tag: `theorem-t-proof-freeze-2026-09-09`.
All frozen relative paths below are relative to
`THEOREM_T_FREEZE_2026-09-09_212604/`.

| Dependency | SHA-256 | Use |
|---|---|---|
| `rwa_proof/sources/grushin1971.pdf` | `c5901af60d30b3a41a7e4a62576cfd1689bcd11ce7097c84299c3077534da93e` | Primary printed pp. 179–183, directly inspected as page images; exact norm and comparison recurrence |
| `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` | Model maximal estimate U2–U5 and target U1/U12 |
| `rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` | Physical normalized Grushin context |
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | Preserved theorem boundary |

The primary paper is V. V. Grušin, *On a class of elliptic
pseudodifferential operators degenerate on a submanifold*, Math. USSR
Sbornik 13 (1971), 155–185,
[DOI 10.1070/SM1971v013n02ABEH001033](https://doi.org/10.1070/SM1971v013n02ABEH001033).
The local archived primary PDF was available; the argument above does not
depend on an inaccessible source.

New sealed dependency in this directory:
`GRUSHIN_H12_WEAK_INITIALIZATION_v1.md`, SHA-256
`ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812`.
Its root review is `GRUSHIN_H12_ROOT_REVIEW_v1.md`, SHA-256
`2d1beaef6db29634e0d59a2c8b7af7c8a925e8b9ab64799f2b29b7bd8ba13536`.

The auxiliary `grushin_recurrence_checks_v1.py` exhaustively checks a
finite range of the integer cost identities, all 498 norm triples,
componentwise regrouping choices, and the exact finite geometric identity.
The general proofs are Sections 4–8; testing does not prove the infinite
statements and is not a mathematical axiom or an energy certificate.

No frozen artifact has been edited. No counterexample to the inherited
operator conclusion was found. The direct finite sum (R22) avoids any
dependence on the compressed geometric-series line on the primary paper's
printed p. 183. Review status and final hashes are recorded separately when
this new proof is sealed.
