import HomogeneousSpectatorSeriesDerivative_v1

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
#check @TheoremT.Continuum.polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial_coarse
#check @TheoremT.Continuum.homogeneousSpectatorSum_eventuallyEq_grouped
#check @TheoremT.Continuum.homogeneous_spectator_series_quarter_domain_factorial_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.polynomialCoeffL1_groupedHomogeneousSpectatorPolynomial_coarse
#print axioms TheoremT.Continuum.homogeneousSpectatorSum_eventuallyEq_grouped
#print axioms TheoremT.Continuum.homogeneous_spectator_series_quarter_domain_factorial_bound
