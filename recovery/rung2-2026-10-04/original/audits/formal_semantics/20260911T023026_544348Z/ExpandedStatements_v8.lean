import HomogeneousSpectatorSumAnalytic_v1
import HomogeneousSpectatorRescaling_v1
import SpectatorScalingMap_v1
import HomogeneousSpectatorAnisotropicAnalytic_v1

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
#check @TheoremT.Continuum.homogeneousSpectatorSum
#check @TheoremT.Continuum.homogeneous_spectator_sum_analytic_isotropic
#check @TheoremT.Continuum.homogeneous_polynomial_eval_scale
#check @TheoremT.Continuum.rescaledHomogeneousSpectatorFamily
#check @TheoremT.Continuum.rescaledHomogeneousSpectatorFamily_isHomogeneous
#check @TheoremT.Continuum.rescaledHomogeneousSpectatorFamily_eval
#check @TheoremT.Continuum.polynomialCoeffL1_rescaledHomogeneousSpectatorFamily
#check @TheoremT.Continuum.spectatorScalingMap
#check @TheoremT.Continuum.spectatorScalingMap_analyticAt
#check @TheoremT.Continuum.spectatorScalingMap_inverse_cancel
#check @TheoremT.Continuum.spectatorScalingMap_inverse_norm_le_one
#check @TheoremT.Continuum.homogeneousSpectatorSum_rescaling
#check @TheoremT.Continuum.exists_positive_larger_geometric_radius
#check @TheoremT.Continuum.homogeneous_spectator_sum_analytic_anisotropic

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.homogeneousSpectatorSum
#print axioms TheoremT.Continuum.homogeneous_spectator_sum_analytic_isotropic
#print axioms TheoremT.Continuum.homogeneous_polynomial_eval_scale
#print axioms TheoremT.Continuum.rescaledHomogeneousSpectatorFamily
#print axioms TheoremT.Continuum.rescaledHomogeneousSpectatorFamily_isHomogeneous
#print axioms TheoremT.Continuum.rescaledHomogeneousSpectatorFamily_eval
#print axioms TheoremT.Continuum.polynomialCoeffL1_rescaledHomogeneousSpectatorFamily
#print axioms TheoremT.Continuum.spectatorScalingMap
#print axioms TheoremT.Continuum.spectatorScalingMap_analyticAt
#print axioms TheoremT.Continuum.spectatorScalingMap_inverse_cancel
#print axioms TheoremT.Continuum.spectatorScalingMap_inverse_norm_le_one
#print axioms TheoremT.Continuum.homogeneousSpectatorSum_rescaling
#print axioms TheoremT.Continuum.exists_positive_larger_geometric_radius
#print axioms TheoremT.Continuum.homogeneous_spectator_sum_analytic_anisotropic
