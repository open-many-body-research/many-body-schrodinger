import KSRealSpectatorSeriesData_v1
import KSRealSpectatorSeriesDescent_v1

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
#check @TheoremT.Continuum.ksRealSpectatorFamilyA
#check @TheoremT.Continuum.ksRealSpectatorFamilyB
#check @TheoremT.Continuum.ks_real_spectator_series_data
#check @TheoremT.Continuum.ks_real_spectator_series_analytic
#check @TheoremT.Continuum.ks_real_spectator_series_norm_bounds
#check @TheoremT.Continuum.ks_real_spectator_series_uniform_convergence
#check @TheoremT.Continuum.ks_real_spectator_series_physical_descent

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksRealSpectatorFamilyA
#print axioms TheoremT.Continuum.ksRealSpectatorFamilyB
#print axioms TheoremT.Continuum.ks_real_spectator_series_data
#print axioms TheoremT.Continuum.ks_real_spectator_series_analytic
#print axioms TheoremT.Continuum.ks_real_spectator_series_norm_bounds
#print axioms TheoremT.Continuum.ks_real_spectator_series_uniform_convergence
#print axioms TheoremT.Continuum.ks_real_spectator_series_physical_descent
