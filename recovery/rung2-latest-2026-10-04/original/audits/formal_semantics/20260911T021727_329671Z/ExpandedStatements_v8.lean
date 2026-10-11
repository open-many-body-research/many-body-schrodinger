import HomogeneousSpectatorSeriesMajorant_v1
import HomogeneousSpectatorSeriesConvergence_v1
import ShiftedHomogeneousSpectatorSeries_v1

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
#check @TheoremT.Continuum.homogeneousSpectatorTerm
#check @TheoremT.Continuum.homogeneousSpectatorMajorant
#check @TheoremT.Continuum.spectator_monomial_norm_bound
#check @TheoremT.Continuum.homogeneous_spectator_term_norm_bound
#check @TheoremT.Continuum.homogeneous_spectator_majorant_hasSum
#check @TheoremT.Continuum.homogeneous_spectator_majorant_summable
#check @TheoremT.Continuum.homogeneous_spectator_series_closed_polydiscs
#check @TheoremT.Continuum.shifted_homogeneous_spectator_series_closed_polydiscs

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.homogeneousSpectatorTerm
#print axioms TheoremT.Continuum.homogeneousSpectatorMajorant
#print axioms TheoremT.Continuum.spectator_monomial_norm_bound
#print axioms TheoremT.Continuum.homogeneous_spectator_term_norm_bound
#print axioms TheoremT.Continuum.homogeneous_spectator_majorant_hasSum
#print axioms TheoremT.Continuum.homogeneous_spectator_majorant_summable
#print axioms TheoremT.Continuum.homogeneous_spectator_series_closed_polydiscs
#print axioms TheoremT.Continuum.shifted_homogeneous_spectator_series_closed_polydiscs
