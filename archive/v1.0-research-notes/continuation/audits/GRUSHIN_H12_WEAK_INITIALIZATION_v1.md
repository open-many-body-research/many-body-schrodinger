> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit weak H12 initialization for the normalized KS operator

Date: 2026-09-09. Evidence: **paper theorem for actual L² distributional solutions**, with an explicit finite derivative schedule and constants. No Lean verification, proof of the full analytic recurrence, or unconditional physical RWA theorem is asserted.

The precise frozen target is `UNIFORM_ANALYTIC_AUDIT.md`, U7–U11, lines 166–250, used by `RWA_THEOREM.md`, lines 164–170. The new result supplies the missing explicit derivative reserve and removes any need to invoke qualitative analytic hypoellipticity to license the bootstrap. Partial mollification in the tangential variables commutes with the model operator and permits a weak proof throughout.

The conclusion is a quantitative H¹² estimate from the L² norm of a distributional solution, eleven derivatives of the source, and eleven bounded derivatives of the zeroth-order coefficient. Exactly twelve tangential gain steps and five ordinary y-elliptic recovery steps suffice, on 34 predetermined spatial gaps. No smallness of the potential is needed for this **finite-order** estimate. The separate small-perturbation absorption used in Grušin's factorial recurrence is not removed by this result.

## 1. Exact theorem and an explicit constant

Let y∈R⁴, t∈R³, c>0, and

\[
P_c=-\Delta_y-c|y|^2\Delta_t,\qquad Q=P_c+B(y,t).
\]

Use a product box

\[
\Omega_0=(-a_y,a_y)^4\times\bigl(t_0+(-a_t,a_t)^3\bigr),
\]

and target box Ω_* with the same center and positive half-widths b_y<a_y, b_t<a_t. Let

\[
\delta=\frac{\min(a_y-b_y,a_t-b_t)}{34}>0,
\quad R=2a_y,
\quad \Omega_j=(-a_y+j\delta,a_y-j\delta)^4
\times\bigl(t_0+(-a_t+j\delta,a_t-j\delta)^3\bigr).
\tag{H1}
\]

Thus Ω_*⊆Ω₃₄ and |y|≤R on Ω₀. Intermediate fractional subscripts mean the same continuous shrinking rule.

Suppose B∈C¹¹(Ω₀;C), with

\[
b_0=\|B\|_\infty<\infty,
\qquad K=\max_{|\eta|\le11}\|D^\eta B\|_\infty<\infty,
\]

f∈H¹¹(Ω₀), v∈L²(Ω₀), and Qv=f in distributions on Ω₀. Set

\[
F_{11}=\max_{|\eta|\le11}\|D^\eta f\|_{L^2(\Omega_0)},
\qquad D=\|v\|_{L^2(\Omega_0)}+F_{11}.
\tag{H2}
\]

The derivatives of f here are actual weak Sobolev derivatives; the coefficient need not be analytic for this finite-order result.

Define the following finite positive constants solely from the displayed data:

\[
L_1=24/\delta,\qquad L_2=1200/\delta^2,
\]

\[
E_c=\sqrt{1+4L_1^2(1+cR^2)},\qquad
J_c=1+2L_1(1+\sqrt cR)E_c+L_2(1+cR^2),
\]

\[
G_c=1+E_c+\left((4\sqrt c)^{-1}+\sqrt{3/2}\right)J_c,
\quad L=(1+b_0)G_c,
\quad A_t=L(2+2^{11}K),
\tag{H3}
\]

\[
E_y=\sqrt{1+4L_1^2},\quad
J_y=1+2L_1E_y+L_2,\quad L_y=1+E_y+J_y,
\]

\[
C_R=3c(R^2+20R+90)+2^{10}K,
\qquad A_y=L_y(2+C_R).
\tag{H4}
\]

Then v∈H¹²(Ω_*) and, for the Sobolev norm that sums squared L² norms of all multi-index derivatives of total order at most twelve,

\[
\boxed{\displaystyle
\|v\|_{H^{12}(\Omega_*)}
\le \sqrt{50388}\,A_y^5 A_t^{12}\,D .}
\tag{H5}
\]

Here 50388=binom(19,7) counts those multi-indices in seven variables. The size of the constant is deliberately conservative. Every dependence on the box separation, c, and the finite coefficient norms is displayed. No coefficient derivative beyond order eleven is used; no unknown derivative norm of v occurs on the right.

## 2. Fixed cutoffs and the compact-support model estimate

All cutoff choices are made before choosing a solution or scaling parameter. For each adjacent pair of half-gap boxes, form tensor products of the scalar C² step

\[
\Theta(s)=\begin{cases}
0,&s\le0,\\
10s^3-15s^4+6s^5,&0<s<1,\\
1,&s\ge1.
\end{cases}
\]

It satisfies 0≤Θ≤1, |Θ′|≤2 and |Θ″|≤15. A product of its left and right transitions across width δ/2 has first derivative at most 8/δ and second derivative at most 152/δ². Tensoring in seven coordinates gives the safe bounds

\[
|\nabla_y\chi|,|\nabla_t\chi|\le L_1,
\qquad |\Delta_y\chi|,|\Delta_t\chi|\le L_2.
\tag{H6}
\]

At an outer level j, choose η equal to one on Ω_{j+1}, with support in the closure of Ω_{j+1/2}, and χ equal to one on Ω_{j+2}, with support in the closure of Ω_{j+3/2}. These supports are compactly contained in their respective larger boxes. Both cutoffs have (H6). The C² cutoffs and their compactly supported products can be approximated in the required second-order norms by smooth ones; no cutoff has to be differentiated beyond order two in this proof.

The frozen oscillator calculation U2–U3 gives, for compactly supported smooth z,

\[
\|\nabla_tz\|_2\le(4\sqrt c)^{-1}\|P_cz\|_2,
\qquad
\|D_y^2z\|_2\le\sqrt{3/2}\,\|P_cz\|_2.
\tag{H7}
\]

The second norm counts the full ordered y-Hessian. These extend to compactly supported H² functions by ordinary mollification: on a fixed containing box the coefficient |y|² is bounded, and H² convergence gives convergence of P_cz in L². Only this common **model** estimate is used; the perturbed compact-support absorption U6 is unnecessary for (H5).

## 3. Ordinary weak y-elliptic estimate, including its justification

If w,H∈L²(Y_out×T) and −Δ_yw=H distributionally, then on two nested y-gaps with cutoffs as in (H6),

\[
\max\{\|w\|_2,\|\nabla_yw\|_2,\|D_y^2w\|_2\}_{Y_{\rm in}\times T}
\le L_y\bigl(\|w\|_{L^2(Y_{\rm out}\times T)}+
\|H\|_{L^2(Y_{\rm out}\times T)}\bigr).
\tag{H8}
\]

This does not presume w∈H². To prove it, first convolve w and H only in y, using kernels supported in a radius smaller than the unused outer margin. The equation commutes with this convolution. For the regularized functions, testing with η² times their conjugate and taking real parts gives

\[
\|\eta\nabla_yw\|_2^2
\le \|H\|_2^2+(1+4L_1^2)\|w\|_2^2.
\]

Apply the compact y-Fourier identity ||D_y²z||₂=||Δ_yz||₂ to z=χw. Its commutator is −2∇_yχ·∇_yw−(Δ_yχ)w, giving the Hessian bound J_y(||H||₂+||w||₂), and hence (H8). All calculations may first be made on finite L²(T)-valued simple approximations and then passed to the limit, or justified directly by Fubini and Hilbert-space inner products. No t derivative or t boundary integration is involved.

The L² norms of the convolutions do not exceed the original outer-domain norms. Their y derivatives through order two are therefore bounded uniformly as the smoothing radius tends to zero. Weak compactness in the finite product of L² spaces and distributional convergence identify the limits as the weak derivatives of w. This proves (H8) for the original distributional solution. Thus later use of (H8) is not an invocation of an unproved smoothness license.

## 4. A weak local gain for P_c, with no hypoellipticity shortcut

For v,h∈L²(Ω_j) with P_cv=h distributionally,

\[
\max\{\|v\|_2,\|\nabla_yv\|_2,\|\nabla_tv\|_2,\|D_y^2v\|_2\}_{\Omega_{j+2}}
\le G_c\bigl(\|v\|_{L^2(\Omega_j)}+\|h\|_{L^2(\Omega_j)}\bigr).
\tag{H9}
\]

First suppose the integrations below are justified. Put W=||v||_{L²(Ω_j)}, H=||h||_{L²(Ω_j)}. Testing the equation with η²v̄ and using 2ab≤a²/2+2b² yields the weighted energy estimate

\[
\|\eta\nabla_yv\|_2^2+c\|\eta|y|\nabla_tv\|_2^2
\le H^2+[1+4L_1^2(1+cR^2)]W^2.
\tag{H10}
\]

Thus on Ω_{j+1} the combined weighted gradient norm is at most E_c(W+H). The exact cutoff commutator is

\[
[P_c,\chi]v=-2\nabla_y\chi\cdot\nabla_yv-(\Delta_y\chi)v
-2c|y|^2\nabla_t\chi\cdot\nabla_tv-c|y|^2(\Delta_t\chi)v.
\]

Its first-order part is bounded by 2L₁(1+√cR)E_c(W+H); its zeroth-order part by L₂(1+cR²)W. Therefore

\[
\|P_c(\chi v)\|_2\le J_c(W+H).
\]

Applying (H7), along with (H10) and the original L² norm, proves (H9) for this regularized class with exactly the constant in (H3).

For a general L² distributional solution, **convolve in t only**. Extend v,h by zero in t solely to define convolution; choose a compactly supported probability kernel of radius μ<δ/4. This μ is a regularization radius, distinct from the physical scale ε used later. On the fixed region containing the supports of η and χ, the distributional equation is unchanged and

\[
P_cv_\mu=h_\mu.
\tag{H11}
\]

This commutation is exact because every coefficient of P_c depends only on y. The zero extension introduces no term in this interior equation: the convolution test functions remain strictly inside the original t-box. Young's inequality gives ||v_μ||₂≤W and ||h_μ||₂≤H on the regions used.

For each fixed μ, every t derivative of v_μ and h_μ is locally L². In particular

\[
-\Delta_yv_\mu=c|y|^2\Delta_tv_\mu+h_\mu\in L^2_{\rm loc}.
\]

Estimate (H8) gives local y-H². Applying (H8) also to its first t derivatives gives the mixed derivatives needed for joint local H². These preliminary norms may diverge as μ→0, but they are used only to justify integrations. The energy and maximal-estimate argument (H10)–(H11) then gives the **uniform** bound (H9), using only W and H, not those preliminary norms. Compact support and H² approximation justify applying (H7) to χv_μ.

Finally v_μ→v locally in L². Weak compactness of the uniformly bounded first derivatives and y-Hessians identifies their distributional limits, proving (H9) for v. This is a regularization proof of the exact quantitative estimate. It uses neither Grušin's analytic theorem nor Hörmander's qualitative smoothness theorem, and does not assume the desired H¹ or H²_y conclusion as an input.

For Qw=g, simply apply (H9) to P_cw=g−Bw. Since ||g−Bw||₂≤||g||₂+b₀||w||₂,

\[
\max\{\|w\|_2,\|\nabla_yw\|_2,\|\nabla_tw\|_2,\|D_y^2w\|_2\}_{\Omega_{j+2}}
\le L(\|w\|_{L^2(\Omega_j)}+\|g\|_{L^2(\Omega_j)}).
\tag{H12}
\]

No restriction such as εM C_P<1/2 occurs in this finite-order estimate.

## 5. Twelve tangential steps and their exact reserve

For a tangential multi-index β with |β|=k≤11, distributional differentiation and the weak product rule give

\[
Q D_t^\beta v=D_t^\beta f-
\sum_{0<\eta\le\beta}\binom\beta\eta
(D_t^\eta B)D_t^{\beta-\eta}v.
\tag{H13}
\]

Assume the tangential derivatives through k are bounded on Ω_{2k} by A_t^kD. This holds at k=0. Every v derivative on the right of (H13) has strictly smaller tangential order, and the coefficient derivatives have order at most eleven. Since Σ_{η≤β}binom(β,η)=2^k, the right side is bounded in L²(Ω_{2k}) by

\[
F_{11}+(2^k-1)K A_t^kD.
\]

Applying (H12) on Ω_{2k}→Ω_{2k+2} bounds D_t^βv, each next tangential derivative, each first y derivative, and each second y derivative by

\[
L\{F_{11}+[1+(2^k-1)K]A_t^kD\}\le A_t^{k+1}D.
\tag{H14}
\]

The last inequality follows from A_t≥1, F₁₁≤D, k≤11, and the definition of A_t. Thus the induction is strictly triangular in tangential order. It does not ask for D_t^(k+1)v in the kth right side.

After k=0,…,11, restriction to Ω₂₄ gives:

* every pure tangential derivative of order ≤12;
* every derivative with one y derivative and tangential order ≤11;
* every derivative with two y derivatives and tangential order ≤11;

all bounded by A_t¹²D in L². In particular the entire set

\[
\{D_y^\alpha D_t^\beta v:|\alpha|\le2,
\ |\alpha|+|\beta|\le12\}
\tag{H15}
\]

is controlled. The one-y-derivative reserve at tangential order eleven is important: it supplies the highest total-order odd-y derivatives at the starting level without demanding a thirteenth pure t derivative.

## 6. Five y-elliptic levels, including the odd-order case

For j=1,…,6 define the derivative family

\[
\mathcal S_j=\{(\alpha,\beta):|\alpha|\le2j,
\ |\alpha|+|\beta|\le12\}.
\]

At level j use box Ω_{24+2(j−1)}. We prove by induction that every derivative in S_j has L² norm at most

\[
E_j=A_y^{j-1}A_t^{12}D.
\tag{H16}
\]

The case j=1 is (H15). For j≤5, take any new target (α′,β)∈S_{j+1} with |α′|>2j. Choose γ≤α′ with |γ|=2 and put α=α′−γ. Then

\[
|\alpha|\in\{2j-1,2j\},\qquad
|\alpha|+|\beta|\le10,
\]

so w=D_y^αD_t^βv is already in S_j. This choice covers **both** odd and even new y orders; an induction using only |α|=2j would miss the boundary family |α′|=2j+1, |β|=11−2j.

Differentiate the actual equation as a y-elliptic equation:

\[
-\Delta_yw=cD_y^\alpha(|y|^2\Delta_tD_t^\beta v)
-D_y^\alpha D_t^\beta(Bv)+D_y^\alpha D_t^\beta f.
\tag{H17}
\]

The first term expands exactly as

\[
\begin{split}
D_y^\alpha(|y|^2\Delta_tD_t^\beta v)
={}&|y|^2\Delta_tD_y^\alpha D_t^\beta v\\
&+2\sum_i\alpha_i y_i\Delta_tD_y^{\alpha-e_i}D_t^\beta v\\
&+\sum_i\alpha_i(\alpha_i-1)\Delta_tD_y^{\alpha-2e_i}D_t^\beta v.
\end{split}
\tag{H18}
\]

Only terms with nonnegative multi-indices are included. Every v derivative on this right side has y order at most 2j and total order at most |α|+|β|+2≤12. They belong to S_j and are already controlled on the larger box. Thus the top term costs two tangential derivatives but **no** uncontrolled new y derivative.

There are three terms in each t-Laplacian, |α|≤10, Σ_iα_i=|α|, and Σ_iα_i(α_i−1)≤90. Hence the first term of (H17) has norm at most 3c(R²+20R+90)E_j. The Bv product has total differentiation order at most ten; its binomial coefficient sum is at most 2¹⁰ and all its v derivatives lie in S_j, giving bound 2¹⁰K E_j. The source derivative is bounded by F₁₁. Therefore

\[
\|\Delta_yw\|_2\le F_{11}+C_RE_j.
\tag{H19}
\]

Apply the weak y-elliptic estimate (H8), with t left as a parameter, on the next two y-gaps and then restrict the t-box to the next level. Its output includes D_y^γw=D_y^{α′}D_t^βv and is bounded by

\[
L_y\{F_{11}+(1+C_R)E_j\}\le A_yE_j=E_{j+1}.
\]

Previously known derivatives remain bounded after restriction, since A_y≥1. This proves (H16) through j=6, on Ω₃₄, where S₆ contains **every** total derivative of order at most twelve. Summing their squared component bounds proves (H5).

The derivative schedule is finite and acyclic. It uses source/coefficient derivatives through eleven in the tangential part and through ten in the y-recovery part. All source indices and all prerequisites of (H18) can be enumerated; the supporting script `grushin_h12_schedule_checks_v1.py` performs this finite combinatorial check. That script is not a verification of the analytic estimates.

## 7. Instantiation for the actual scaled KS difference

Suppose the actual physical ψ is Lipschitz near the triple collision with constant L_ψ, and its lifted equation on the normalized chart is the distributional equation in frozen R3 or R5. Let ψ₀=ψ(0), u_ε the actual KS pullback at physical scale ε, and

\[
v_\varepsilon=(u_\varepsilon-\psi_0)/\varepsilon,
\quad B_\varepsilon=\varepsilon b_\varepsilon,
\quad Q_\varepsilon v_\varepsilon=-\psi_0 b_\varepsilon.
\tag{H20}
\]

Assume the stated uniform chart bound ||D^ηb_ε||∞≤M A^|η||η|! for |η|≤11, A≥1, 0<ε≤ε₀. This bound follows from the separated analytic spectator denominators in the specified charts; no derivative of the Coulomb pole survives after its exact KS clearing. Put

\[
K=\varepsilon_0MA^{11}11!,\qquad b_0=\varepsilon_0M.
\]

Let T₀=|t₀|+√3a_t and V₀=|Ω₀|. Denote the quadratic KS map here by KS(y), distinct from the scalar coefficient bound K above. In a nuclear chart the original normalized physical arguments have norm at most D_X=√(R⁴+T₀²); in an electron-pair chart they have norm at most D_X=√(2T₀²+R⁴/2), from x₁=t+KS(y)/2 and x₂=t−KS(y)/2. Since |KS(y)|=|y|²,

\[
\|v_\varepsilon\|_{L^2(\Omega_0)}\le V_0^{1/2}L_\psi D_X,
\qquad
F_{11,\varepsilon}\le V_0^{1/2}|\psi_0|MA^{11}11!.
\tag{H21}
\]

Consequently, with c=4 in the nuclear case or c=1 in the pair case, (H5) gives the explicit uniform bound

\[
\|v_\varepsilon\|_{H^{12}(\Omega_*)}
\le\sqrt{50388}\,A_y^5A_t^{12}V_0^{1/2}
\bigl(L_\psi D_X+|\psi_0|MA^{11}11!\bigr),
\tag{H22}
\]

independent of ε. This supplies the finite initialization U11 for the **actual** lifted solution once the physical Lipschitz input and weak KS equation are available. It is not an artificial smooth surrogate: the weak-limit argument identifies the derivatives of that original L² distribution.

The distinct remaining tasks are the weak KS transformation from the physical domain, the external physical Lipschitz regularity result in the declared normalization, Grušin's all-order factorial recurrence with its exact weighted norms, and the subsequent quantitative descent and boundary compatibility. None is replaced by the assertion of H¹². In particular this artifact does not itself discharge the full physical G1.

## 8. Targeted adversarial outcome and provenance

No circularity or false inherited conclusion was established in the finite initialization. The frozen text's claim that a sufficiently large finite tangential reserve suffices can be made precise by (H13)–(H19). A naive even-only y-recovery argument would miss highest-total-order odd-y derivatives, but the explicit triangular family S_j avoids that mistake. The main new mathematical content is the all-weak proof and a fully specified finite derivative budget, so qualitative analytic hypoellipticity is unnecessary here.

All frozen paths are relative to `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. The following recomputed hashes matched the manifest:

| Frozen relative path | SHA-256 | Exact coverage |
|---|---|---|
| `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` | Lines 1–340 read; target U7–U11, model input U2–U3. |
| `rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` | Lines 70–215; normalized physical equation and use of initialization. |
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | Previously read target and dependency boundary. |

A qualitative alternative was examined during this targeted work: [Hörmander, *Hypoelliptic second order differential equations*, Theorem 1.1 and (1.6)](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6044-11511_2006_Article_BF02392081.pdf). The indexed primary text gives the sum-of-squares bracket criterion including a smooth zeroth-order term. The four ∂_{y_i} fields and brackets [∂_{y_1},√c y₁∂_{t_j}]=√c∂_{t_j} would give the necessary rank seven. Full PDF retrieval returned HTTP 500; the publisher page provided metadata and an access restriction. That external theorem is **not a dependency of the final proof**, which uses partial convolution and (H8) instead. No inaccessible proof is silently counted as verified.

The new proof and finite schedule checker are separate from every sealed preceding artifact. There is no inherited false-claim correction entry because no such error was confirmed. The next analytic obligation after this initialization is the exact all-order factorial recurrence and its uniform constants; it must not be inferred from twelve derivatives alone.

The parent agent's independent review is recorded in `GRUSHIN_H12_ROOT_REVIEW_v1.md`. The completed theorem, finite dependency checker and output, and frozen source checks are bound by `GRUSHIN_H12_PROVENANCE_v1.json`. Review agreement and the finite index check are supporting evidence; neither is a kernel proof of the PDE estimates.
