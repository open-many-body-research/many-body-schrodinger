import PhysicalKSAxisRetainedRadius_v1
import SO2PolynomialSeriesInput_v1
import PhysicalKSAxisPlaneSeriesData_v1

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
#check @TheoremT.Continuum.physicalKSAxisSeriesRate_pos
#check @TheoremT.Continuum.physicalKSAxisSeriesRate_mul_analyticAxisRadius_le_half
#check @TheoremT.Continuum.physicalKSAxisSeriesRate_mul_retainedRadius_le_one
#check @TheoremT.Continuum.SO2PolynomialSeriesInput
#check @TheoremT.Continuum.so2PolynomialSeriesInput_of_joint_polynomials
#check @TheoremT.Continuum.physicalKSAxisPlanePolynomialA
#check @TheoremT.Continuum.physicalKSAxisPlanePolynomialB
#check @TheoremT.Continuum.physicalKSAxisPlaneSeries_data
#check @TheoremT.Continuum.nuclearKSPhysicalAxisPlaneSeries_data
#check @TheoremT.Continuum.pairKSPhysicalAxisPlaneSeries_data

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSAxisSeriesRate_pos
#print axioms TheoremT.Continuum.physicalKSAxisSeriesRate_mul_analyticAxisRadius_le_half
#print axioms TheoremT.Continuum.physicalKSAxisSeriesRate_mul_retainedRadius_le_one
#print axioms TheoremT.Continuum.SO2PolynomialSeriesInput
#print axioms TheoremT.Continuum.so2PolynomialSeriesInput_of_joint_polynomials
#print axioms TheoremT.Continuum.physicalKSAxisPlanePolynomialA
#print axioms TheoremT.Continuum.physicalKSAxisPlanePolynomialB
#print axioms TheoremT.Continuum.physicalKSAxisPlaneSeries_data
#print axioms TheoremT.Continuum.nuclearKSPhysicalAxisPlaneSeries_data
#print axioms TheoremT.Continuum.pairKSPhysicalAxisPlaneSeries_data
