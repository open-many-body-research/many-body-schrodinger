> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# R9 base profile from a genuine finite H12 budget

Let an actual finite weak H12 derivative family of raw f on open Ω have squared L2 budget W for every derivative through total order12. Let F be a separately chosen natural derivative family of the same f, with genuine weak Y/T chains through that order; equality of the base representatives is needed only locally almost everywhere. If |y|≤S on Ω and S≥1, then for every r≤8 and every O⊆Ω,

N_r(F,O) ≤ 498 S² sqrt(W).

Here N_r is the existing actual finite maximum of local outer norms over natural base indices with cost ω(a,b)=|a|+|b|+min(|a|,4)≤r. Each outer norm is the sum of the 498 prescribed monomial-weighted restricted L2 norms. The proof first identifies the finite H12 family with F by genuine local weak uniqueness, retaining W. The base total derivative order is at most r; an outer component adds at most2, hence all used derivatives have order≤10. A monomial of degree≤2 is bounded by S². Its actual L2 representative is constructed from the restricted derivative field, and its norm is bounded by S²sqrt(W). Summing498 components and taking the finite maximum gives the stated constant.

The theorem proves every required weighted field belongs to L2 before interpreting its eLpNorm.toReal. It also constructs the shifted weighted representatives with norm equal to the actual local outer norm. One raw F is fixed before allr and subregions; the Lp representatives may depend on r and the region. The proof handles W=0 without division. A generic helper works whenever r+2≤the available finite derivative order.

Three new modules and six declarations compile and pass strictv7 expanded-statement and axiom audits with only propext, Classical.choice and Quot.sound. The independently sealed finite-budget transfer supplies actual cross-family identification. Lean4.34.0-rc2 reused pinned dependency objects; no isolated source rebuild. Independent exact-source review found no defect. There were no compiler failures in this unit.

The physical R01 H12 budget and actual all-order raw family remain separately proved inputs for application. This unit discharges their conversion to the consumed R9 base bound, not the later factorial recurrence or full TheoremT.
