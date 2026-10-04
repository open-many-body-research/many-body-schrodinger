import ScalarSpectatorGeometricSeries_v1

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
#check @TheoremT.Continuum.scalarSpectatorPolynomialFamily
#check @TheoremT.Continuum.scalarSpectatorPolynomialFamily_isHomogeneous
#check @TheoremT.Continuum.scalarSpectatorPolynomialFamily_coeffL1_le
#check @TheoremT.Continuum.scalarSpectatorTerm
#check @TheoremT.Continuum.scalarSpectatorSum
#check @TheoremT.Continuum.scalarSpectatorTerm_eq
#check @TheoremT.Continuum.scalarSpectatorSum_eq
#check @TheoremT.Continuum.scalar_spectator_sum_analytic
#check @TheoremT.Continuum.scalar_spectator_series_closed_polydiscs

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.scalarSpectatorPolynomialFamily
#print axioms TheoremT.Continuum.scalarSpectatorPolynomialFamily_isHomogeneous
#print axioms TheoremT.Continuum.scalarSpectatorPolynomialFamily_coeffL1_le
#print axioms TheoremT.Continuum.scalarSpectatorTerm
#print axioms TheoremT.Continuum.scalarSpectatorSum
#print axioms TheoremT.Continuum.scalarSpectatorTerm_eq
#print axioms TheoremT.Continuum.scalarSpectatorSum_eq
#print axioms TheoremT.Continuum.scalar_spectator_sum_analytic
#print axioms TheoremT.Continuum.scalar_spectator_series_closed_polydiscs
