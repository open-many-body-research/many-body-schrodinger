# S2: Two-electron theory and "Theorem T"

**Scope.** Two electrons and one nucleus of charge $Z$ (He, H⁻, Li⁺, …). This sector covers existence, simplicity and gaps of the ground state, spectral separators, and the complexity of certified ground-energy computation.

## The target: Theorem T (OPEN)

> **Theorem T (conjectured).** For each fixed $Z \ge 2$ there is a deterministic algorithm that, on input $p$, outputs rationals $\ell \le E_Z \le u$ with $u-\ell \le 2^{-p}$, using at most $C_Z (p+1)^{d}$ bit operations for some fixed $d$.

**Status: open.** A report in the private pre-foundation work once labeled Theorem T "PROVEN" with $d = 2256$. That label was wrong and has been withdrawn ([ERRATUM-001](../../errata/ERRATUM-001-theorem-t-not-proved.md)). These pieces are still missing:

1. A **human-reviewed** proof of the analytic inputs: triple-collision regularity (S8.1) and the dictionary approximation rate (S8.3).
2. A coefficient-selection algorithm with a correctness proof (S2.2).
3. Verified moment evaluation and a finite solver, with a termination proof.
4. An operational bit-cost model.
5. The composition of all of the above.

Even if it were finished, $C_Z$ would not be explicit and the exponent would not be practical. Theorem T is a complexity statement, not a practical method.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S2-001 | **Abstract continuum Temple.** Suppose $\beta\|x\|^2 \le \operatorname{Re}\langle x,Hx\rangle + C|\ell(x)|^2$ on $D(H)$, and a unit $\psi \in D(H)$ has mean $L \le \mu \le U < \beta$ and $\|H\psi-\mu\psi\|^2 \le r$. Then $\inf\sigma(H) \in [L - r/(\beta-U),\, U]$, and the ground state is attained and simple. | L (the form comparison is a *premise*) |
| S2-002 | **Two-electron ground branch.** For real $Z$ with $9Z^2 > 32$ (which includes helium), the physical two-electron operator attains its bottom $E < -5Z^2/8$. The ground eigenspace is one complex line, and every other spectral value has real part $\ge -5Z^2/8$. For helium: $E_\text{He} < -5/2$, and the rest of the spectrum lies at $\operatorname{Re} z \ge -5/2$. | L |
| S2-003 | **Helium enclosure implication.** For every certified unit $H^2$ trial with mean in $[L, U]$, $U < -5Z^2/8$, and squared residual $\le r$, the true ground energy lies in $[L - r/(-5Z^2/8-U),\, U]$. | L (the trial data are premises; see S2.3) |
| S2-004 | **Rank-one separator for integer $Z \ge 2$:** $H_Z \ge -Z^2P_0 - \tfrac58 Z^2(I-P_0)$, hence $\beta = -5/2$ for helium. | P1 (reviewed by AI agents only), and covered in Lean by S2-002 |
| S2-005 | **Separator for real $Z > (20+5\sqrt{10})/24$,** using the $Z - 5/16$ screened trial. | P1 |
| S2-006 | **Variance-selection counterexample.** Exact global variance minimization over nested spaces can select an excited state. | P1 |
| S2-007 | **Fixed-shift selection.** Minimizing $\|(H-\sigma)\varphi\|^2$ with $\sigma$ below the spectrum selects the ground branch. Together with density, this makes $E_Z$ computable (no cost bound). | P1 |

**Classical background.** The separator in S2-004 is Bazley's intermediate-problem method and Temple's inequality is from 1928. What's new here is the formal (Lean) treatment of the unbounded continuum operator.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S2.1 | **Theorem T** (as stated above) | A full proof at tier P2, then Lean | open |
| S2.2 | **Coefficient selection.** Show that the regularized fixed-shift pencil solve on the dictionary $V_n$ returns a vector whose certified Temple width is $\le K\cdot(\text{best residual})^2 + 2^{-n}$, with polynomial bit cost per stage. | P2 proof | open |
| S2.3 | **Close the loop in Lean.** Instantiate S2-003 with a concrete low-order Hylleraas trial by formalizing its moments, which lie in the rational span $\mathbb Q+\mathbb Q\log 2+\mathbb Q\pi^2$. | A Lean theorem `E_He ∈ [ℓ, u]` with rational $\ell, u$, width $< 10^{-2}$, standard axioms only | open |
| S2.4 | **Sharpen S2-002.** Its hypothesis $9Z^2 > 32$ comes from the crude bound $R_Z^2 \le Z^2/2$. Using the exact repulsion $5Z/8$ would extend it to the full range $Z > Z^*$ of S2-005. | Lean | open |

## Where to look
- **Lean:** `lean/Foundation/CoulombRankOneBranch_v1.lean`, `CoulombRankOneCertificate_v1.lean`, `TwoElectronPhysicalGroundBranch_v1.lean`, `TwoElectronGroundMultiplicity_v1.lean`, `TwoElectronPhysicalCertificate_v1.lean`.
- **Research notes:** [`archive/v1.0-research-notes/`](../../archive/v1.0-research-notes/). Relevant files are `TWO_ELECTRON_THEOREM.md`, `RWA_REPORT.md` (historical; it contains the withdrawn "PROVEN" claim) and `continuation/paper/TWO_ELECTRON_PHYSICAL_COMPARISON_v1.md`.
