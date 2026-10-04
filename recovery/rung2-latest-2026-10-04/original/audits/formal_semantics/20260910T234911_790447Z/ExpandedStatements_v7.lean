import ProductWeakFiniteFamilyUnique_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
set_option maxRecDepth 16384
set_option pp.rawOnError true
#check @TheoremT.Continuum.WeakGrushin.product_local_weak_word_families_unique
#check @TheoremT.Continuum.WeakGrushin.product_mixed_multiIndex_weak_families_unique
#check @TheoremT.Continuum.WeakGrushin.RegionL2Budget.congr_ae

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.product_local_weak_word_families_unique
#print axioms TheoremT.Continuum.WeakGrushin.product_mixed_multiIndex_weak_families_unique
#print axioms TheoremT.Continuum.WeakGrushin.RegionL2Budget.congr_ae
