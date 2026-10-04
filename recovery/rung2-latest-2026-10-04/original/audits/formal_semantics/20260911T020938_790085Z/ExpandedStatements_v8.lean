import ComplexPowerSeriesCenterDerivativeBound_v1

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
#check @TheoremT.Continuum.complex_powerSeries_iteratedFDeriv_eq_permutation_sum
#check @TheoremT.Continuum.complex_powerSeries_norm_iteratedFDeriv_le_factorial_coeff

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.complex_powerSeries_iteratedFDeriv_eq_permutation_sum
#print axioms TheoremT.Continuum.complex_powerSeries_norm_iteratedFDeriv_le_factorial_coeff
