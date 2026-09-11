> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Common physical KS factorial coefficient bounds

For fixed real Z,E, there exist C,A >= 1 chosen before either selected nuclear electron i : Fin 2, the pair chart, every unit physical spectator center, every eps in [0,1], every derivative order or ordered word, every point, every complex amplitude a0 and every measurable subregion S. The constants are obtained from the true analytic compact estimates on the three fixed annuli, using one finite common majorant indexed by Fin 2 sum Unit. The compact regions do not depend on the center or derivative order.

For each chart, b_eps is exactly nuclearKSPotential i Z (eps*E) or pairKSPotential Z (eps*E). The actual iterated Frechet derivative norms of b_eps, eps*b_eps, and b_eps smul (-a0) are bounded by C*A^k*k!, eps*(C*A^k*k!), and (C*A^k*k!)*norm(a0), respectively. In particular the full physical coefficient retains eps and its energy contribution contains eps squared. No inverse eps is introduced, and eps=0 is allowed.

The same C,A controls arbitrary ordered physical coordinate words with no dimension factor. It also controls every mixed Y/T word of total order k. For every measurable S within the applicable region, the actual mixed normalized source has RegionL2Budget (C*A^k*k!)^2 * norm(a0)^2 * (volume S).toReal. This is a squared L2 budget with the actual product volume measure. Region measurability is explicit, and finite volume follows from inclusion in the compact annulus. The budget leaves its exact region-volume factor visible; this theorem does not assert a separately evaluated common numerical volume.

The physical-center endpoint uses the exact inverse image under physicalSpectatorReindexAt i of rectangularOpenBox (0,t0) (1/64) (1/64), for every Position t0 of norm one. The pair endpoint uses i=0 reindexing, definitionally equal to the existing pair-center map. The arbitrary seven-coordinate word helper maps spectator letters through (twoElectronSpectatorCoordinateEquiv i).symm. No spectator spaces are silently identified and no derivative commutation is assumed. The common annuli include y=0 wherever their actual nuclear/pair patches allow it.

Main APIs in namespace TheoremT.Continuum:

- ksCommonAnnulus_uniform_factorial_jets and ksCommonAnnulus_uniform_factorial_physical_boxes.
- ksCommonAnnulus_uniform_factorial_jet_word_control and ksCommonAnnulus_uniform_factorial_physical_box_data.
- ksScaledFactorialWordControl_physical_word for the explicit seven-coordinate-to-physical-word mapping.
- KSScaledFactorialJetControl and KSScaledFactorialWordControl contain the full quantified bounds; subset lemmas retain the same constants.

Validation: both new modules compiled using check_module_v2.py and the pinned dependency cache. Approved v7 audit formal_semantics/20260910T232217_548837Z/receipt.json passed all 11 declarations with only propext, Classical.choice and Quot.sound, complete axiom reporting, no forbidden source tokens, printer ellipses or printer-failure diagnostics, and unchanged source/object hashes. All expanded types and full axiom reports were read. The actual values of both new control predicates were additionally printed and read in KS_COMMON_ANNULUS_FACTORIAL_DEFINITIONS_v2 using the approved printer options, with zero ellipses and no error/failure diagnostics. The earlier optional definitions print v1 is preserved but not used as complete evidence because pp.proofs=false suppressed proof arguments; no mathematical source change was needed.

Independent focused read-only review by /root/finite_affine_jets/physical_direction_norm matched both source hashes and read the definitions and supporting finite-majorant, scaled coefficient, mixed-region budget and annulus-inclusion bodies. It found no quantifier, scaling, source-sign, measure, coordinate or scope defect. The reviewer ran no compiler/auditor and edited no files.

These are actual coefficient and normalized forcing estimates, with existential constants. They do not prove solution analyticity, a factorial PDE induction, descent, evaluated constants, a certified algorithm, or original T02. Z,E remain fixed before the constants. No frozen or prior PASS artifact, historical audit, or shared ledger was changed. No source dependency rebuild, broad audit, SSH or Colab operation was performed.

Historical context: frozen relative path rwa_proof/THEOREM_T_COMPOSITION.md; SHA-256 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da; commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09; inventory THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json.
