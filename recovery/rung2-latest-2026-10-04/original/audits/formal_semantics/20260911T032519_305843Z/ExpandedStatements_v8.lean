import SO2DescendedSeriesRadius_v1

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
#check @TheoremT.Continuum.so2_descended_coefficient_rate
#check @TheoremT.Continuum.so2_descended_series_analytic
#check @TheoremT.Continuum.so2_descended_series_half_polyradii

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2_descended_coefficient_rate
#print axioms TheoremT.Continuum.so2_descended_series_analytic
#print axioms TheoremT.Continuum.so2_descended_series_half_polyradii
