import PhysicalKSAxisPlaneSeriesInvariance_v1
import PhysicalKSPlanePolynomialBalancedSupport_v1

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
#check @TheoremT.Continuum.so2JointRealProduct
#check @TheoremT.Continuum.so2JointComplexProduct
#check @TheoremT.Continuum.so2JointRealProduct_norm_le
#check @TheoremT.Continuum.so2JointComplexProduct_norm_le
#check @TheoremT.Continuum.so2JointComplexProduct_elim
#check @TheoremT.Continuum.so2JointComplexProduct_rotation
#check @TheoremT.Continuum.physicalKSAxisPlanePolynomial_balanced_support
#check @TheoremT.Continuum.nuclearKSPhysicalAxisPlanePolynomial_balanced_support
#check @TheoremT.Continuum.pairKSPhysicalAxisPlanePolynomial_balanced_support

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2JointRealProduct
#print axioms TheoremT.Continuum.so2JointComplexProduct
#print axioms TheoremT.Continuum.so2JointRealProduct_norm_le
#print axioms TheoremT.Continuum.so2JointComplexProduct_norm_le
#print axioms TheoremT.Continuum.so2JointComplexProduct_elim
#print axioms TheoremT.Continuum.so2JointComplexProduct_rotation
#print axioms TheoremT.Continuum.physicalKSAxisPlanePolynomial_balanced_support
#print axioms TheoremT.Continuum.nuclearKSPhysicalAxisPlanePolynomial_balanced_support
#print axioms TheoremT.Continuum.pairKSPhysicalAxisPlanePolynomial_balanced_support
