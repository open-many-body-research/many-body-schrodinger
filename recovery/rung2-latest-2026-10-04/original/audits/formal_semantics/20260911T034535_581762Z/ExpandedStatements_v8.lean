import SO2AxisPolynomialRestriction_v1
import SO2AxisGroupedSeries_v1
import SO2AxisGroupedAnisotropic_v1
import PhysicalKSAxisPolynomialData_v1

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
#check @TheoremT.Continuum.so2AxisPolynomialGenerator
#check @TheoremT.Continuum.so2AxisPolynomialRestriction
#check @TheoremT.Continuum.so2AxisPolynomialGenerator_homogeneous
#check @TheoremT.Continuum.so2AxisPolynomialGenerator_coeffL1
#check @TheoremT.Continuum.so2AxisPolynomialRestriction_homogeneous
#check @TheoremT.Continuum.so2AxisPolynomialRestriction_coeffL1
#check @TheoremT.Continuum.so2AxisPolynomialRestriction_eval
#check @TheoremT.Continuum.so2AxisGroupedPolynomial
#check @TheoremT.Continuum.so2AxisGroupedPolynomial_homogeneous
#check @TheoremT.Continuum.so2AxisGroupedPolynomial_coeffL1
#check @TheoremT.Continuum.so2_axis_coordinate_norm_le
#check @TheoremT.Continuum.so2AxisGroupedPolynomial_hasSum
#check @TheoremT.Continuum.homogeneous_spectator_coefficient_max_rate
#check @TheoremT.Continuum.so2AxisGroupedPolynomial_coeffL1_anisotropic
#check @TheoremT.Continuum.so2AxisGroupedPolynomial_hasSum_anisotropic
#check @TheoremT.Continuum.physicalKSAxisPolynomialA
#check @TheoremT.Continuum.physicalKSAxisPolynomialB
#check @TheoremT.Continuum.physicalKSAxisSeriesRate
#check @TheoremT.Continuum.PhysicalKSAxisPolynomialData
#check @TheoremT.Continuum.physicalKSAxisPolynomial_data_of_balanced
#check @TheoremT.Continuum.nuclearKSPhysicalAxisPolynomial_data
#check @TheoremT.Continuum.pairKSPhysicalAxisPolynomial_data

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2AxisPolynomialGenerator
#print axioms TheoremT.Continuum.so2AxisPolynomialRestriction
#print axioms TheoremT.Continuum.so2AxisPolynomialGenerator_homogeneous
#print axioms TheoremT.Continuum.so2AxisPolynomialGenerator_coeffL1
#print axioms TheoremT.Continuum.so2AxisPolynomialRestriction_homogeneous
#print axioms TheoremT.Continuum.so2AxisPolynomialRestriction_coeffL1
#print axioms TheoremT.Continuum.so2AxisPolynomialRestriction_eval
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial_homogeneous
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial_coeffL1
#print axioms TheoremT.Continuum.so2_axis_coordinate_norm_le
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial_hasSum
#print axioms TheoremT.Continuum.homogeneous_spectator_coefficient_max_rate
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial_coeffL1_anisotropic
#print axioms TheoremT.Continuum.so2AxisGroupedPolynomial_hasSum_anisotropic
#print axioms TheoremT.Continuum.physicalKSAxisPolynomialA
#print axioms TheoremT.Continuum.physicalKSAxisPolynomialB
#print axioms TheoremT.Continuum.physicalKSAxisSeriesRate
#print axioms TheoremT.Continuum.PhysicalKSAxisPolynomialData
#print axioms TheoremT.Continuum.physicalKSAxisPolynomial_data_of_balanced
#print axioms TheoremT.Continuum.nuclearKSPhysicalAxisPolynomial_data
#print axioms TheoremT.Continuum.pairKSPhysicalAxisPolynomial_data
