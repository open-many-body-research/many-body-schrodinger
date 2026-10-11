import KSRealPolynomialToSpinor_v1

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
#check @TheoremT.Continuum.ksSpinorInversePolynomial
#check @TheoremT.Continuum.ksRealPolynomialToSpinor
#check @TheoremT.Continuum.ksSpinorInversePolynomial_homogeneous
#check @TheoremT.Continuum.ksSpinorInversePolynomial_physical_eval
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_physical_eval
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_homogeneous
#check @TheoremT.Continuum.polynomialCoeffL1_ksSpinorInversePolynomial
#check @TheoremT.Continuum.polynomialCoeffL1_ksRealPolynomialToSpinor

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksSpinorInversePolynomial
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor
#print axioms TheoremT.Continuum.ksSpinorInversePolynomial_homogeneous
#print axioms TheoremT.Continuum.ksSpinorInversePolynomial_physical_eval
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_physical_eval
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_homogeneous
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksSpinorInversePolynomial
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRealPolynomialToSpinor
