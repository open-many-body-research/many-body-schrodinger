> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local potential reduction for the actual Grushin operator

The two new modules prove local L² closure and the exact equivalence

\[
 (P_c+B)f=g\quad\Longleftrightarrow\quad P_cf=g-Bf
\]

in the compact-test sense, where the actual implemented operator is

\[
 P_c=-\Delta_y-c|y|^2\Delta_t.
\]

The reduction uses `KSSpace × T` with its actual product Lebesgue measure,
finite-dimensional real inner-product spectator space `T`, and any finite
orthonormal basis. The raw functions (f,g) are complex and only locally L² on

(\Omega).

The real coefficient (B) is assumed continuous on (Omega); no global
continuity, global measurability, or global L² hypothesis is imposed on it or on

(Bf).

The coefficient closure lemmas apply more generally to finite-dimensional
products `Y × T`. On each compact (K\subseteq\Omega), continuity makes

(B\in L^\infty(K)).

Actual `MemLp.smul` then gives (Bf\in L^2(K)), and subtraction gives

(g-Bf\in L^2(K)).

For a smooth compact real test (phi) supported inside (Omega), the proof
establishes integrability of all five expressions

\[
 (P_c+B)\phi\,f,\quad P_c\phi\,f,\quad\phi g,
 \quad\phi Bf,\quad\phi(g-Bf).
\]

The actual `splitGrushin` definition gives the pointwise algebraic identity

\[
 ((P_c+B)\phi)f=(P_c\phi)f+\phi(Bf).
\]

Only after proving integrability does the proof split or subtract the integrals.
No derivative of (B) is taken, and no coefficient is commuted through a
mollifier. The argument works for arbitrary real (c) and even arbitrary
sets (Omega); open regions are included.

The main API is

```lean
grushin_local_potential_reduction c b hB f g hf hg h
```

It returns both `ProductLocallyL2On (fun p => g p - B p • f p) Ω` and the
corresponding zero-potential compact-test equation. The `_iff` theorem proves
both directions. These lemmas supply the source term for the separately proved
local Grushin regularity result; they do not assume or establish that regularity
by themselves and are not an executable PDE solver.

Both modules compiled, and the joint nine-declaration strict audit
`formal_semantics/20260910T175543_571909Z/receipt.json` passed with complete
expanded statements, no ellipses, and only `propext`, `Classical.choice`, and
`Quot.sound`. Pinned development objects were reused; this is not a new source
dependency rebuild. Source, object, compilation receipt, and strict audit hashes
are preserved in `GRUSHIN_LOCAL_POTENTIAL_REDUCTION_CHECKPOINT_v1.json`, SHA-256
`8ede66175f478d313b71b553e762fd913f37f0a4f65ca12b3a5c9773049cee4c`.
