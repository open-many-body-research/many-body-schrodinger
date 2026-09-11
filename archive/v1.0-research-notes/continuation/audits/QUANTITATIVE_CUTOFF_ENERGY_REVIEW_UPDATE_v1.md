> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Review update: completed uniform cutoff output

The four modules initially pending in the focused review have now passed their
strict audits and have been reviewed. The cumulative scope is **20 modules and
66 declarations across eight strict receipts**, without recompilation or edits.
No defect was found. The initial review remains unchanged; exact added source,
object, and receipt fingerprints are in
`QUANTITATIVE_CUTOFF_ENERGY_REVIEW_UPDATE_v1.json`.

`WeakGrushinCutoffOutputNormAux_v1` proves the conditional squared bound with
coefficients (2,4,16). `WeakGrushinCutoffOutputNorm_v1` derives its exact
almost-everywhere output formula from the local PDE and genuine global weak H²
jets, constructs the cutoff principal output in actual L², and supplies its
global compact-test PDE. Their strict receipt is
`formal_semantics/20260910T174440_455037Z/receipt.json`.

`WeakGrushinCutoffLocalData_v1` chooses the middle plateau cutoff and its energy
constant (E) before quantifying over (f,h). The outer plateau and weak jets
are chosen later, but are compared to the energy of that fixed middle cutoff.
Consequently their dependence on the supplied local weak H² data does not enter
the constant. The restricted function norm is compared with the original global
L² norm only after proving almost-everywhere equality on the compact set.

`WeakGrushinCutoffUniformOutput_v1` chooses the fixed cutoff bounds (M,A,B)
and (E) before (f,h), then sets

\[
 C=3M^2+4A^2+16BE\ge0.
\]

Its constructed actual L² cutoff and output satisfy

\[
 \|U\|_2^2\le C\|f\|_2^2,
 \qquad \|H\|_2^2\le C(\|f\|_2^2+\|h\|_2^2).
\]

Indeed the preceding estimate has coefficients

\[
 (4A^2+16BE)\|f\|_2^2+(2M^2+16BE)\|h\|_2^2,
\]

each at most (C). The additional (M^2) is harmless; no optimality is claimed.
These last two modules have strict receipt
`formal_semantics/20260910T174708_982206Z/receipt.json`.

The remaining hypotheses are explicit: (c\ge0), fixed smooth compact cutoff
inside an open set, globally actual L² (f,h), local weak H² for (f), and the
local weak Grushin equation. No first-derivative bound is assumed. Removing the
local weak H² premise through regularization and limiting arguments, and
composing the separate local-L² extension, remain the next obligations.

A second agent independently challenged the compact anisotropic bound and its
direct weighted-integrability/energy dependencies. That review also found no
defect, confirmed the constants and true integrability of the discarded terms,
and confirmed that the theorem remains an a priori estimate for H² input.
