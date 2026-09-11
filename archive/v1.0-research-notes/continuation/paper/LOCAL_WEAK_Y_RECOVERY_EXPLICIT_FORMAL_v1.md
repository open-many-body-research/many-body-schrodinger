> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit weak Y recovery for the finite H12 schedule

Evidence: fully formalized local PDE prerequisites; not a completed H12 theorem.

For open Ω⊂R⁴×R^κ, raw local L² functions w,H, and genuine raw local first and same-second spectator jets of w, the actual equation −ΔY w=H implies local joint weak H². Two weak compact-test integrations prove Δ(Y,T)w=−H+Σ_j eT,j. All test products are integrable by compact local L² restrictions, and the existing full product elliptic theorem constructs the preliminary derivatives. No Y derivative is assumed.

For supplied smooth compact χ,η and an open W with suppχ⊂W and η=1 on W, let η be supported strictly inside Ω. Assume |χ|≤M, |combinedCutoffScalar(0,χ)|≤A and cutoffGradientWeight(0,χ)≤L on suppχ, η²≤D and grushinCutoffWeight(0,η)≤Q globally, with L,D,Q≥0. Before any raw data, choose compact K⊂Ω and an open intermediary V containing suppη. Put

    F=∫K|w|²,  H2=∫K|H|²,
    J=(4A²+16L(D/2+Q))F+(2M²+8LD)H2.

The theorem constructs U=χw almost everywhere and actual compatible Y-first and all ordered YY weak derivatives with

    ||U||²≤M²F,
    Σ||D_Y U||²≤2M²F+3J/4,
    ΣΣ||D_Y D_Y U||²≤3J/2.

The genuine T/T² jets establish preliminary joint H² only; their norms do not enter J. The quantitative step specializes the proved compact weak Grushin output and energy estimates to c=0. The auxiliary K,V and preliminary local regularity introduce no additional quantitative cutoff gap beyond the two supplied χ,η. The coefficient is a proved variant for the finite recovery program; the earlier paper H8/H4 numerical constants are not asserted unchanged.

The accompanying generic product relation ProductLocalWeakDirectional includes local L² of both functions and the actual real compact-test identity. Its swap theorem proves D_v(D_w f)=e from genuine D_vf=dv, D_wf=dw and D_wdv=e. This uses symmetry of smooth test-function second derivatives. Global-to-local restriction, monotonicity, test integrability and the local smooth-coefficient product rule are also supplied. This supports mixed finite derivative families without assuming their compatibility.

For the H12 schedule, each w=DY^α DT^β G with |α|∈{2j−1,2j} and |α|+|β|≤10 has the required T² reserve in the already known Sj family. Covering both values of |α| is necessary for odd new Y orders. The actual differentiated RHS and the finite five-level composition remain to be formalized. Under P_c=−ΔY−c|y|²ΔT, the correct undifferentiated RHS is −ΔY G=source−BG+c|y|²ΔT G; no source file implements the earlier mistaken negative sign shorthand.

All four new modules and eleven declarations compiled and passed reviewed-v5 expanded-statement/axiom audits. Only propext, Classical.choice and Quot.sound occur, with unchanged source/object hashes. Pinned caches were reused; no new isolated source rebuild was run. These modules are outside the earlier 671-target snapshot. Choices remain analytic existence data, not executable coefficient selection. No all-order factorial, global approximation, spectral, numerical or full Theorem T claim is made.
