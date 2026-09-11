> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Genuine local weak H² regularity for homogeneous Grushin solutions

Evidence category: fully compiled and axiom-audited mathematical theorem for
an actual continuum weak PDE. This theorem has no input derivative assumption.
It proves qualitative local weak H², without an analyticity or algorithm claim.

## Exact theorem

Let X=R^4×R^m with actual product Lebesgue measure, c>0, Ω⊂X open, and B:X→R
smooth on Ω. Let G:X→C be locally L² on Ω. Suppose

∫_X (P_cφ+Bφ)G = 0,
P_c=-Δ_y-c|y|²Δ_t,

for every real smooth compact test φ with supp φ⊂Ω. Then G has genuine local
weak H² on Ω.

The exact formal meaning is `ProductLocalWeakH2On G Ω`: for every real smooth
compact cutoff χ supported in Ω, there exist an actual global product-measure
L² class U=χG almost everywhere, actual L² first derivative classes d(v) for
every product direction v, and an actual L² weak derivative of d(v) in every
ordered direction w. Each weak derivative is verified against all real smooth
compact tests. Thus the statement includes every ordered second derivative,
including mixed Y/T derivatives. Neither global L² of the original G nor any
input first or second derivative is assumed. The raw function may be arbitrary
outside Ω; every test and cutoff used in the theorem is supported inside Ω.

The Lean module is `LocalWeakGrushinHomogeneousH2_v1`; the theorem is
`TheoremT.Continuum.WeakGrushin.local_weak_grushin_homogeneous_h2`.

## Proof structure

Fix χ. Choose an outer smooth compact cutoff ρ and an open neighborhood V with
supp χ⊂V⊂Ω and ρ=1 on V. The previously verified first Grushin gain, applied to
raw local L² G with zero forcing, constructs an actual global L² class
G₀=ρG and actual weak Y first, Y second, and T first derivatives. At this stage
no T second or mixed Y/T derivative is assumed or inferred.

Locality of the full Grushin test expression, including Bφ, transfers the
original equation to G₀ on V. It uses the equality G₀=G on V and does not
differentiate ρ outside the plateau.

For each spectator coordinate t_j, the actual weak product rule and spectator
commutation derive

(P_c+B)(D_tj G₀)=-(D_tj B)G₀

on V. The right side is locally L² because B is locally smooth and G₀ is L².
Apply the first Grushin gain again to D_tj G₀. This gives a genuine first
spectator derivative of a further localized D_tj G₀. The nested single-direction
weak cutoff product rule combines this with the known derivative of G₀ to
produce a genuine diagonal second t_j derivative of χG₀.

The already available diagonal Y second derivatives yield the corresponding
Y diagonal derivatives of χG₀. All these diagonals are genuine weak derivatives
of the same L² class. Their sum supplies the actual full Euclidean product
Laplacian in L². The previously proved product Laplacian converse and global
elliptic gain then provide all first and ordered second derivatives, including
mixed derivatives. Finally χG₀=χG almost everywhere by the plateau identity.

The second-gain theorem records precisely its intermediate assumptions:
global L² G₀ with Y and T first derivatives, diagonal YY derivatives, and the
homogeneous local weak equation. It does not assume TT, mixed derivatives, or
H². The final raw-input theorem discharges these intermediate derivative
assumptions using the first gain.

## Evidence and limits

The two endpoint modules and their exact source/object hashes are recorded in
`audits/LOCAL_WEAK_GRUSHIN_HOMOGENEOUS_H2_CHECKPOINT_v1.json`. Both final statements
compile, with complete expanded statements and axiom reports containing only
propext, Classical.choice and Quot.sound. The root proof and wrapper were read
directly; an independent review of the wrapper checked its support nesting,
raw-versus-global L² distinction, quantifier meaning, positivity of c, and
absence of an assumed H² premise. Kernel checking, not reviewer agreement, is
the verification mechanism.

Development used Lean 4.34.0-rc2 with pinned cached Mathlib and previously
compiled continuation dependencies. These endpoint modules and recent
prerequisites postdate the completed 671-target desktop isolated source
rebuild; this checkpoint is not a new isolated source rebuild.

No H² constant or quantitative H² estimate is asserted by this endpoint. The
first-gain estimates are separate proved results. No smoothness, analyticity,
factorial recurrence, approximation rate, Coulomb spectral identification,
certified energy computation, executable algorithm, complexity bound, novelty,
or full Theorem T is claimed here. Applying the result to physical KS pullbacks
requires their actual local L² membership and the exact weak transformed PDE;
that is a separate composition obligation.

The preserved original claim source is `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. No frozen or earlier successful artifact was
modified.
