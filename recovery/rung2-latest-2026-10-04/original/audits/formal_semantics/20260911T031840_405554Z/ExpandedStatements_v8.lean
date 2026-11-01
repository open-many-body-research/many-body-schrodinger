import PhysicalKSBoxAnalyticDescentData_v2
import CoulombSpinPhysicalAnalyticDescent_v2
import TwoElectronGroundPhysicalAnalyticDescent_v2

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
#check @TheoremT.Continuum.PhysicalKSBoxAnalyticDescentDerivativeData
#check @TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_derivative_data
#check @TheoremT.Continuum.pairKSPhysicalAnalyticDescent_derivative_data
#check @TheoremT.Continuum.coulomb_spin_physical_analytic_descent_derivative_representative
#check @TheoremT.Continuum.twoElectron_physical_ground_analytic_descent_derivative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.PhysicalKSBoxAnalyticDescentDerivativeData
#print axioms TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_derivative_data
#print axioms TheoremT.Continuum.pairKSPhysicalAnalyticDescent_derivative_data
#print axioms TheoremT.Continuum.coulomb_spin_physical_analytic_descent_derivative_representative
#print axioms TheoremT.Continuum.twoElectron_physical_ground_analytic_descent_derivative
