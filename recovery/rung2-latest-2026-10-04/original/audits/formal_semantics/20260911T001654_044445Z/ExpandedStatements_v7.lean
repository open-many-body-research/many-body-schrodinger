import ProductCompactWeakWordGlobal_v1

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
#check @TheoremT.Continuum.directionalWordDeriv_tsupport_subset
#check @TheoremT.Continuum.directionalWordProduct_support_subset
#check @TheoremT.Continuum.product_compact_local_weak_word_family_global
#check @TheoremT.Continuum.product_compact_cutoff_finite_weak_word_family

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.directionalWordDeriv_tsupport_subset
#print axioms TheoremT.Continuum.directionalWordProduct_support_subset
#print axioms TheoremT.Continuum.product_compact_local_weak_word_family_global
#print axioms TheoremT.Continuum.product_compact_cutoff_finite_weak_word_family
