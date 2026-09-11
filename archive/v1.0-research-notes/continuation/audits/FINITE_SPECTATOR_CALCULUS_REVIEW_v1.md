> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Finite spectator calculus: bounded adversarial review v1

Date: 2026-09-10. Reviewer: `/root/local_elliptic_gain/product_local_h2`.

**Finding:** no mathematical or semantic defect was found in the six exact sources below. The endpoint proves a finite conditional differentiation theorem for genuine local weak derivative families. It does not construct those families or establish higher regularity from the original PDE alone.

This was a read-only review of PASS sources, followed by creation of this note. No build or dependency audit was rerun. The reviewer authored the raw-local Leibniz module; the other five modules were authored by the coordinating agent, so this is not an independent review of every dependency. The coordinating agent reported their PASS status. The raw-local module's strict receipt was separately checked at `formal_semantics/20260910T191419_607441Z/receipt.json`: five expanded declarations, complete axiom reports, only `propext`, `Classical.choice`, and `Quot.sound`, zero printer ellipses, and unchanged source/object hashes. The combined v4 strict audit is separate evidence and was pending when this note was written. Pinned dependency objects were reused for the reported builds.

## Exact reviewed sources

Paths are relative to `../lean/` from this note.

| Module | SHA-256 |
| --- | --- |
| `ProductLocalWeakDirectionalLeibniz_v1.lean` | `14e54cbb74625ca299861b342e7fc7029b9b0f0f0f770d8260de9ae45527c582` |
| `SpectatorWordSplits_v1.lean` | `72d901fabda19287368f4fc7f8cdb59e9ec7cf1328d1123700f8b694e15409c5` |
| `SpectatorWordProduct_v1.lean` | `372fe2a2238399cfb6890237efc1bed5779448b99af6b4a31237580bf8af5f27` |
| `LocalSpectatorDerivativeAlgebra_v1.lean` | `d6723439b743865f196c65077a067a7df2f7a07f67d41cafe597637b4f417862` |
| `SpectatorWordWeakLeibniz_v1.lean` | `3535a8acd23b1e4d24f562dd6409a5a33a537b04c573066842b4e3a7e5a751b9` |
| `WeakGrushinFiniteSpectatorEquation_v1.lean` | `370836b5063353ce404ff34b5d0de022705b9bbc14c0bca1ccecbb3eba471f63` |

## Statement and hypotheses

On the actual product space `Space κ = ℝ⁴ × EuclideanSpace ℝ κ`, let Ω be open, B real and C∞ on Ω, c any real number, and m finite. The principal operator is `P_c = −Δ_y − c‖y‖²Δ_t`; the actual tested operator includes the potential B. The supplied families G_w and F_w are raw functions, locally L² on Ω for every word of length at most m. Explicit compact-test identities identify G_(j::w) and F_(j::w) with the spectator weak derivatives of G_w and F_w whenever |w| < m. Only the empty-word equation `(P_c+B)G_[]=F_[]` is assumed.

For each |w| ≤ m, `weak_grushin_finite_spectator_equations` derives the actual compact-test equation

`(P_c+B)G_w = F_w − Σ_(a,b in properSplits(w)) (D_a B) G_b`,

including local L² membership of the right side and integrability of both tested sides. The list sum retains all split occurrences. Each summand has |a| > 0, |b| < |w|, and |a|+|b|=|w|.

## Attempts to invalidate the argument

- **Word orientation.** `j::w` means the outer derivative `D_j(D_w)`. Both coefficient and solution subwords receive the new j by cons. This preserves the order of each chosen subsequence; no permutation or commutativity of weak derivatives is assumed by the combinatorial argument.
- **Repeated directions.** Splits are lists, and `List.map` followed by `List.sum` keeps duplicate occurrences. For `[j,j]`, the four choices are `([j,j],[])`, `([j],[j])`, `([j],[j])`, and `([],[j,j])`; the middle term therefore has coefficient 2. The proved length is exactly `2^|w|`.
- **Removal of the all-solution term.** The exact list identity is `splits(w)=properSplits(w)++[([],w)]`. The strictness theorem excludes an empty coefficient word from every proper split, so one complete occurrence of `B G_w` is removed and every remaining solution order is smaller. This remains true for the empty word, whose proper list is empty.
- **Finite-order indexing.** At a step with |w|<m, every solution subword b of a split of w satisfies |b|≤|w|<m. Hence the required next word j::b has length at most m. The main list induction similarly derives |w|<m from |j::w|≤m. The case m=0 uses only the given empty-word equation.
- **Actual local derivatives and integrability.** `LocalSpectatorD` contains the genuine test identity but does not itself include local L². Additive and finite-sum uses supply the separate local L² premises and justify the integrals before applying integral algebra. The raw-local Leibniz proof tests the given derivative with φB; local smoothness and test support prove this is a globally smooth compact test supported in Ω. Compact restriction proves all required test products integrable. No global L² representative or global derivative is assumed.
- **Circular higher PDE or wrong sign.** The main proof sets `H_w=F_w−Product_w`, derives its derivative chain by the local Leibniz theorem, and proves `P_c G_w=H_w` by induction. The step invokes the previously proved principal spectator commutation. Reintroducing the potential leaves `F_w−properCommutator_w`, with the displayed minus sign. No positive-word PDE is an input. The exact imported principal differentiation and potential-reduction interfaces were inspected for this composition.

## Remaining frontier

The supplied weak derivative families through order m are substantive regularity hypotheses. This result alone gives neither their existence for a given rough solution nor one family of every order. It gives no derivative norm estimates, factorial recurrence, analytic radius, pointwise smooth representative, uniform domain estimates, or computation. Arbitrary real c is correct for this differentiation algebra; a coercive regularity argument requires its own hypotheses, including any needed positivity. The next bootstrap must establish its missing derivatives and their bounds without treating this conditional finite calculus as that existence theorem. No novelty claim is made.
