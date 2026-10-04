import PhysicalKSBoxPointwiseFactorial_v1
import CoulombKSPhysicalPointwise_v1

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
#check @TheoremT.Continuum.physicalKSPointwiseRate
#check @TheoremT.Continuum.physicalKSPointwiseAmplitude
#check @TheoremT.Continuum.physicalKSPointwiseRate_pos
#check @TheoremT.Continuum.physicalKSPointwiseAmplitude_nonneg
#check @TheoremT.Continuum.physicalKSBoxFactorialData_smooth_pointwise
#check @TheoremT.Continuum.physicalKSBoxFactorialData_analytic
#check @TheoremT.Continuum.PhysicalKSBoxPointwiseData
#check @TheoremT.Continuum.physicalKSBoxFactorialData_to_pointwise
#check @TheoremT.Continuum.scalar_coulomb_all_physical_box_pointwise

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSPointwiseRate
#print axioms TheoremT.Continuum.physicalKSPointwiseAmplitude
#print axioms TheoremT.Continuum.physicalKSPointwiseRate_pos
#print axioms TheoremT.Continuum.physicalKSPointwiseAmplitude_nonneg
#print axioms TheoremT.Continuum.physicalKSBoxFactorialData_smooth_pointwise
#print axioms TheoremT.Continuum.physicalKSBoxFactorialData_analytic
#print axioms TheoremT.Continuum.PhysicalKSBoxPointwiseData
#print axioms TheoremT.Continuum.physicalKSBoxFactorialData_to_pointwise
#print axioms TheoremT.Continuum.scalar_coulomb_all_physical_box_pointwise
