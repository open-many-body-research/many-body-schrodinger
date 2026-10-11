import HomogeneousSpectatorNormalizedDerivative_v1

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
#check @TheoremT.Continuum.homogeneousSpectatorSum_normalized_eq
#check @TheoremT.Continuum.polynomialCoeffL1_normalizedHomogeneousSpectatorFamily
#check @TheoremT.Continuum.spectatorScalingMap_norm_le_of_blocks
#check @TheoremT.Continuum.homogeneous_spectator_normalized_quarter_domain_factorial_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.homogeneousSpectatorSum_normalized_eq
#print axioms TheoremT.Continuum.polynomialCoeffL1_normalizedHomogeneousSpectatorFamily
#print axioms TheoremT.Continuum.spectatorScalingMap_norm_le_of_blocks
#print axioms TheoremT.Continuum.homogeneous_spectator_normalized_quarter_domain_factorial_bound
