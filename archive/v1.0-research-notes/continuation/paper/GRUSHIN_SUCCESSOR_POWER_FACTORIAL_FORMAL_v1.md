> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Shift-one factorial conversion

The compiled theorem `grushin_successor_core_power_factorial_bound` proves, for every natural r,

    (r+1)^r ≤ 3^(r+1) r!.

The proof bounds the single nonnegative exponential-series term (r+1)^r/r! by exp(r+1), rewrites exp(r+1)=exp(1)^(r+1), and uses the exact proved inequality exp(1)<3. Multiplication is only by the positive factorial; there is no division by r.

The compiled theorem `grushin_r23_factorial_bound` takes ρ>0, B≥0, S≥0 and

    N ≤ 2 B S (2 B (r+1)/ρ)^r

and proves

    N ≤ 6 B S (6 B/ρ)^r r!.

It factors the initial power and multiplies the first inequality by a nonnegative factor. It never divides by S or B. Consequently r=0, B=0 and S=0 are included in the exact theorem. N need not be assumed nonnegative. This is a numerical implication; application to an actual profile still requires the previously proved R23 bound. No pointwise bound or Theorem T conclusion is asserted by this unit.

Evidence: compilation PASS and strict v7 audit PASS for both exact statements, receipt `audits/formal_semantics/20260911T002804_398347Z/receipt.json`. The complete expanded statements were read. Axioms are only propext, Classical.choice and Quot.sound. Pinned caches were reused; this is not a new isolated dependency rebuild. Prior successful and frozen bytes remain unchanged.
