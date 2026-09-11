> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual finite tangential iteration

The formal endpoint spectatorFiniteState_iterate starts from one raw region-L2 solution f of (P_c+P)f=F_empty, c>0, with no input solution derivative. It uses n supplied cutoff stages. Each stage contains only actual open-region and smooth compact cutoff geometry and the displayed pointwise cutoff coefficient bounds. Nested domains follow from the plateau identities; they are not assumed as a regularity conclusion.

The initial source family F_w must have actual weak spectator derivative identities and a common region-L2 squared budget H0 for every |w|<n. Its derivative edges have |w|+1<n. The real potential P is smooth on the initial region and its actual ordered spectator derivatives through order n-1 have a common pointwise bound K0 there. The original solution has a region-L2 squared budget Winit. These are actual MemLp statements and integral inequalities on the entire initial region, not norms of unspecified representations.

Write R0=Winit. At stage k use its geometry constants M_k,A_k,B_k,D_k,Q_k, and put

C0_k=4A_k²+16B_k(D_k/2+Q_k),
C1_k=2M_k²+8B_kD_k,
J_k(W)=(C0_k+2C1_k K0²)W+2C1_k[2H0+2(2^k-1)²K0²W],
R_(k+1)=R_k+2M_k²R_k+(9/4+1/(16c))J_k(R_k).

Every term is explicit. Nonnegativity of the displayed budgets and B_k,D_k,Q_k makes each next budget nonnegative and at least the previous one. It dominates all Y-first, T-first and ordered YY estimates of that stage. This recurrence is a mathematical bound on norms, not a cost model or executable numerical algorithm.

On the final region Omega_n, the theorem constructs a raw family G_w with G_empty=f and genuine local weak T-word identities through order n. Every G_w with |w|<=n belongs to L2 of that final region and has squared integral at most R_n. For each |w|<n it also retains actual global L2 classes gy_(w,i) and hyy_(w,i,j), with sum_i||gy||²<=R_n and sum_i,j||hyy||²<=R_n. On Omega_n, gy is the genuine Y-first derivative of G_w; globally, hyy is the genuine Y derivative of gy. Earlier words and their witnesses are preserved exactly, and their local equations restrict to the smaller region.

At n=12, only source/coefficient derivatives through eleven are used. The result supplies T words through twelve, Y-first derivatives at every T word through eleven, and YY derivatives at every T word through eleven; the latter includes the required T<=10 family for total order twelve. In particular the odd-Y total-order-twelve endpoint is not lost. R12 bounds each G word separately and each word's Y/YY component sums. It does not yet bound the sum over all spectator words or perform the five higher-Y recovery levels.

The final plateau region is whatever the supplied geometry specifies; this general endpoint does not independently assert its openness, nonemptiness or size. Actual rectangle instantiation must prove its own positive widths and bridge the physical spectator coordinate type to the scheduled three-coordinate space. Uniform physical coefficient/source budgets are also separate inputs. Accordingly this unit is the actual finite tangential initialization, not the full physical H12 theorem, factorial regularity, analyticity or Theorem T.

Six modules and twenty declarations pass strict final expanded-statement/axiom audit with only propext, Classical.choice and Quot.sound. The source-hashed adversarial review checks the no-input-solution-jet baseline, finite derivative budget, preservation and restriction arguments. Evidence and exact source/object hashes are recorded in audits/ACTUAL_FINITE_SPECTATOR_ITERATION_CHECKPOINT_v1.json. Lean4.34.0-rc2 pinned dependency caches were reused; no isolated source rebuild was run for these new modules. All prior successful files remain unchanged. No novelty is claimed.

Frozen RWA_REPORT.md SHA256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, snapshot THEOREM_T_FREEZE_2026-09-09_212604/.
