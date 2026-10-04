import HomogeneousSpectatorRealDerivative_v1

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
#check @TheoremT.Continuum.realMultiindexDeriv
#check @TheoremT.Continuum.realMultiindexDeriv_restriction
#check @TheoremT.Continuum.finite_real_complexification_norm
#check @TheoremT.Continuum.homogeneous_spectator_real_mixed_multiindex_factorial_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.realMultiindexDeriv
#print axioms TheoremT.Continuum.realMultiindexDeriv_restriction
#print axioms TheoremT.Continuum.finite_real_complexification_norm
#print axioms TheoremT.Continuum.homogeneous_spectator_real_mixed_multiindex_factorial_bound
