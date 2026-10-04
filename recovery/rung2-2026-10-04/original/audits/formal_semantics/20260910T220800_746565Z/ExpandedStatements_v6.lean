import AnalyticAffineCompactFactorialJets_v1
import KSScaledFactorialCoefficientBounds_v1

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
#check @TheoremT.Continuum.analytic_affine_compact_factorial_source_bound
#check @TheoremT.Continuum.nuclearKS_energy_coefficient_analyticAt
#check @TheoremT.Continuum.pairKS_energy_coefficient_analyticAt
#check @TheoremT.Continuum.nuclearKS_uniform_factorial_scaled_jets
#check @TheoremT.Continuum.pairKS_uniform_factorial_scaled_jets

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.analytic_affine_compact_factorial_source_bound
#print axioms TheoremT.Continuum.nuclearKS_energy_coefficient_analyticAt
#print axioms TheoremT.Continuum.pairKS_energy_coefficient_analyticAt
#print axioms TheoremT.Continuum.nuclearKS_uniform_factorial_scaled_jets
#print axioms TheoremT.Continuum.pairKS_uniform_factorial_scaled_jets
