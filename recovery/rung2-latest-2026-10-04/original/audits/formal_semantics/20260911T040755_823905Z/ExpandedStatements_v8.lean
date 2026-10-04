import PairDistanceRealAlgebra_v1

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
#check @TheoremT.Continuum.pair_distance_heron_factorization
#check @TheoremT.Continuum.pair_distance_heron_nonneg
#check @TheoremT.Continuum.pair_distance_axis_real_quotient_identity
#check @TheoremT.Continuum.pair_distance_real_transverse_nonneg
#check @TheoremT.Continuum.pair_distance_real_radius_identities
#check @TheoremT.Continuum.pair_distance_real_reconstruction

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.pair_distance_heron_factorization
#print axioms TheoremT.Continuum.pair_distance_heron_nonneg
#print axioms TheoremT.Continuum.pair_distance_axis_real_quotient_identity
#print axioms TheoremT.Continuum.pair_distance_real_transverse_nonneg
#print axioms TheoremT.Continuum.pair_distance_real_radius_identities
#print axioms TheoremT.Continuum.pair_distance_real_reconstruction
