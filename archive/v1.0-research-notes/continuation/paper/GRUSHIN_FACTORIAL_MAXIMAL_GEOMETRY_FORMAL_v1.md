> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual factorial cutoff support constants

For the existing smooth cutoff `factorialRectCutoff a aY aT t e`, assume the Y center is zero, `0 ≤ t`, `0 < e`, and `t+e ≤ ρ < min(aY,aT)`. The compiled theorem `factorialRectCutoff_maximal_geometry` proves that its actual topological support K is compact, lies in the outer open box Ω_t, lies in every Y-coordinate slab of radius R=aY>0, and has Y radius bounded by S=max(1,2aY)≥1. The cutoff equals one on Ω_(t+e).

The coordinate estimate is inherited from the tighter closed support box of half-width aY−t−e/4. Summing the four coordinate squares gives the Y norm bound 2(aY−t−e/4)≤2aY. Nonnegativity of t is an explicit hypothesis needed for constants independent of t. This is a geometric prerequisite for the compact Grushin estimate; it does not assert the profile recurrence or factorial regularity.

Evidence: source compilation PASS and strict v7 exact-statement/axiom audit PASS, receipt `audits/formal_semantics/20260911T002211_536186Z/receipt.json`. The complete expanded statement was inspected. Only propext, Classical.choice and Quot.sound occur. Pinned cached dependencies were reused; this unit has no new isolated source rebuild. Existing successful and frozen artifacts are unchanged.
