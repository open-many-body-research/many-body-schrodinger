import HomogeneousSpectatorFiniteVariables_v1
import PhysicalKSTaylorSpectatorSeries_v1

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
#check @TheoremT.Continuum.homogeneous_spectator_finite_variables_norm_bound
#check @TheoremT.Continuum.homogeneous_spectator_finite_variables_summable
#check @TheoremT.Continuum.physicalKSTaylorSpectatorFamily
#check @TheoremT.Continuum.physicalKSTaylorSpectatorFamily_homogeneous
#check @TheoremT.Continuum.physicalKSTaylorSpectatorFamily_coefficientL1
#check @TheoremT.Continuum.physicalKSTaylorSpectatorFamily_summable

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.homogeneous_spectator_finite_variables_norm_bound
#print axioms TheoremT.Continuum.homogeneous_spectator_finite_variables_summable
#print axioms TheoremT.Continuum.physicalKSTaylorSpectatorFamily
#print axioms TheoremT.Continuum.physicalKSTaylorSpectatorFamily_homogeneous
#print axioms TheoremT.Continuum.physicalKSTaylorSpectatorFamily_coefficientL1
#print axioms TheoremT.Continuum.physicalKSTaylorSpectatorFamily_summable
