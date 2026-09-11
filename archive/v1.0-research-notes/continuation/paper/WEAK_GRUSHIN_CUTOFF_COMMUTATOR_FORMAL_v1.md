> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Cutoff jets and the actual weak Grushin commutator

This continuation establishes a mathematical localization identity for genuine
weak H² inputs. Its derivative hypotheses are actual compact-test weak
derivatives, rather than an assumed operator or commutator formula.

First, on an ordinary Cartesian product Y×T of finite Euclidean spaces, let
f,d(v),e(v,w) be L² functions satisfying Dᵥf=d(v) and D_wd(v)=e(v,w) in all real
smooth compact tests. For every real smooth compact cutoff χ, the theorem
supplies actual L² U,a(v),b(v,w), with U=χf almost everywhere, and proves

    a(v) = χd(v) + (Dᵥχ)f,
    b(v,w) = χe(v,w) + (D_wχ)d(v) + (Dᵥχ)d(w) + (D_wDᵥχ)f.

These are themselves genuine weak first and second derivatives of U. The
construction transports the already verified generic Euclidean cutoff theorem
through the exact WithLp 2 coordinate equivalence. Both the measure and the
first and second chain rules are verified. The ordinary product retains its
maximum norm and actual product Lebesgue measure.

Specialize to Y=R⁴ and T any finite Euclidean coordinate space. For every real
c, write the actual weak principal expression as

    P_c(e) = −Σᵢ e(yᵢ,yᵢ) − c|y|²Σⱼ e(tⱼ,tⱼ).

Define the actual cutoff errors from f and its first weak derivatives by

    C_Y = Σᵢ [(D_yᵢ²χ)f + 2(D_yᵢχ)d(yᵢ)],
    C_T = Σⱼ [(D_tⱼ²χ)f + 2(D_tⱼχ)d(tⱼ)].

The proved cutoff jet formulas imply the almost-everywhere identity

    P_c(b) = χP_c(e) − C_Y − c|y|²C_T.

Each scalar coefficient is continuous and supported in the compact support of
χ or one of its derivatives. Consequently C_Y, C_T, the weighted error
c|y|²C_T, and χP_c(e) all belong to L². The uncut weighted principal expression
P_c(e) is not required to be globally L². The localized principal expression
therefore has a genuine L² representative. Its connection to the weak operator
is the actual compact-test equation obtained from the separately verified
principal-test theorem.

The error expressions agree almost everywhere with the previously formalized
smooth commutator when the weak input representatives equal a smooth function
and its first derivatives. Finite spectator dimension zero and c=0 are included.
No positivity assumption on c is needed for this algebraic result; coercive
Grushin estimates have their own sign hypotheses.

The adjacent checkpoint records six modules and eighteen declarations, with
final source hashes, compiled objects and strict expanded-statement/axiom
receipts. Only propext, Classical.choice and
Quot.sound are permitted. All witnesses are mathematical existence objects.
No executable differentiation or certified numerical computation is asserted.

Development compilation reuses the pinned library and continuation objects;
these new sources are outside the completed 671-target source rebuild. This
result does not provide explicit commutator norm constants, the uniform weak
regularization passage, factorial analytic bounds, or full Theorem T. No
novelty claim is made. The next obligation is the quantitative localization
estimate and its use with compact weak Grushin bounds.

The frozen original RWA_REPORT.md remains unchanged: SHA-256
2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066,
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag
theorem-t-proof-freeze-2026-09-09.
