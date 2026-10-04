import SO2PolynomialSeriesDescent_v1

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
#check @TheoremT.Continuum.so2DescendedCoefficient
#check @TheoremT.Continuum.so2CartesianSeriesTerm
#check @TheoremT.Continuum.so2CartesianSeriesSum
#check @TheoremT.Continuum.so2CartesianSeriesTerm_even
#check @TheoremT.Continuum.so2CartesianSeriesTerm_odd
#check @TheoremT.Continuum.so2_polynomial_series_descent
#check @TheoremT.Continuum.so2_polynomial_descended_sum_analytic

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2DescendedCoefficient
#print axioms TheoremT.Continuum.so2CartesianSeriesTerm
#print axioms TheoremT.Continuum.so2CartesianSeriesSum
#print axioms TheoremT.Continuum.so2CartesianSeriesTerm_even
#print axioms TheoremT.Continuum.so2CartesianSeriesTerm_odd
#print axioms TheoremT.Continuum.so2_polynomial_series_descent
#print axioms TheoremT.Continuum.so2_polynomial_descended_sum_analytic
