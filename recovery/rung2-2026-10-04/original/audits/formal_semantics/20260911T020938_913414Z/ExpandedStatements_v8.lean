import PhysicalKSTaylorCoordinatePolynomials_v1
import KSLocalInvariantPolynomialDescent_v1

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
#check @TheoremT.Continuum.physicalKSTaylorPolynomial
#check @TheoremT.Continuum.physicalKSTaylorPolynomial_homogeneous
#check @TheoremT.Continuum.physicalKSTaylorPolynomial_coefficientL1
#check @TheoremT.Continuum.physicalKSTaylorPolynomial_common_radius
#check @TheoremT.Continuum.ks_local_invariant_polynomial_quantitative_descent

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSTaylorPolynomial
#print axioms TheoremT.Continuum.physicalKSTaylorPolynomial_homogeneous
#print axioms TheoremT.Continuum.physicalKSTaylorPolynomial_coefficientL1
#print axioms TheoremT.Continuum.physicalKSTaylorPolynomial_common_radius
#print axioms TheoremT.Continuum.ks_local_invariant_polynomial_quantitative_descent
