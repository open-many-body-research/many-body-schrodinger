import PhysicalKSBoxInvariantAnalyticDescentData_v1
import TwoElectronScalarGroundInvariantAnalyticDescent_v1

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
#check @TheoremT.Continuum.PhysicalKSBoxInvariantAnalyticDescentDerivativeData
#check @TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_invariant_derivative_data
#check @TheoremT.Continuum.pairKSPhysicalAnalyticDescent_invariant_derivative_data
#check @TheoremT.Continuum.twoElectron_scalar_ground_invariant_analytic_descent_with_H2_decay

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.PhysicalKSBoxInvariantAnalyticDescentDerivativeData
#print axioms TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_invariant_derivative_data
#print axioms TheoremT.Continuum.pairKSPhysicalAnalyticDescent_invariant_derivative_data
#print axioms TheoremT.Continuum.twoElectron_scalar_ground_invariant_analytic_descent_with_H2_decay
