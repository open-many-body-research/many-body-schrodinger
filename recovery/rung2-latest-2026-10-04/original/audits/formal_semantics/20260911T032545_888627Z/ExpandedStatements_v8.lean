import SO2ComplexPolynomialCoordinates_v1
import SO2BalancedHomogeneousPolynomial_v1
import SO2HomogeneousRadialDescent_v1

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
#check @TheoremT.Continuum.so2ForwardPolynomial
#check @TheoremT.Continuum.so2InversePolynomial
#check @TheoremT.Continuum.so2PolynomialToBalanced
#check @TheoremT.Continuum.so2PolynomialToCartesian
#check @TheoremT.Continuum.so2InversePolynomial_forward
#check @TheoremT.Continuum.so2ForwardPolynomial_inverse
#check @TheoremT.Continuum.so2PolynomialToCartesian_toBalanced
#check @TheoremT.Continuum.so2PolynomialToBalanced_toCartesian
#check @TheoremT.Continuum.so2InversePolynomial_homogeneous
#check @TheoremT.Continuum.so2PolynomialToBalanced_homogeneous
#check @TheoremT.Continuum.so2BalancedExponent
#check @TheoremT.Continuum.so2_homogeneous_support_degree
#check @TheoremT.Continuum.so2_balanced_homogeneous_even
#check @TheoremT.Continuum.so2_balanced_homogeneous_odd
#check @TheoremT.Continuum.so2ForwardPolynomial_mul
#check @TheoremT.Continuum.so2PolynomialToCartesian_balanced_power
#check @TheoremT.Continuum.so2_homogeneous_even_radial_descent
#check @TheoremT.Continuum.so2_homogeneous_odd_eq_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2ForwardPolynomial
#print axioms TheoremT.Continuum.so2InversePolynomial
#print axioms TheoremT.Continuum.so2PolynomialToBalanced
#print axioms TheoremT.Continuum.so2PolynomialToCartesian
#print axioms TheoremT.Continuum.so2InversePolynomial_forward
#print axioms TheoremT.Continuum.so2ForwardPolynomial_inverse
#print axioms TheoremT.Continuum.so2PolynomialToCartesian_toBalanced
#print axioms TheoremT.Continuum.so2PolynomialToBalanced_toCartesian
#print axioms TheoremT.Continuum.so2InversePolynomial_homogeneous
#print axioms TheoremT.Continuum.so2PolynomialToBalanced_homogeneous
#print axioms TheoremT.Continuum.so2BalancedExponent
#print axioms TheoremT.Continuum.so2_homogeneous_support_degree
#print axioms TheoremT.Continuum.so2_balanced_homogeneous_even
#print axioms TheoremT.Continuum.so2_balanced_homogeneous_odd
#print axioms TheoremT.Continuum.so2ForwardPolynomial_mul
#print axioms TheoremT.Continuum.so2PolynomialToCartesian_balanced_power
#print axioms TheoremT.Continuum.so2_homogeneous_even_radial_descent
#print axioms TheoremT.Continuum.so2_homogeneous_odd_eq_zero
