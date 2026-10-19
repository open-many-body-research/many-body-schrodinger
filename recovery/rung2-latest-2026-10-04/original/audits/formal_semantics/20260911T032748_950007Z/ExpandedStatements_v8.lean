import SO2FiniteRadialDescent_v1

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
#check @TheoremT.Continuum.so2_balanced_exponent_eq
#check @TheoremT.Continuum.so2PolynomialToCartesian_monomial
#check @TheoremT.Continuum.so2PolynomialToCartesian_balanced_sum
#check @TheoremT.Continuum.so2PolynomialToCartesian_balanced_axis_coeff
#check @TheoremT.Continuum.so2_finite_radial_descent

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2_balanced_exponent_eq
#print axioms TheoremT.Continuum.so2PolynomialToCartesian_monomial
#print axioms TheoremT.Continuum.so2PolynomialToCartesian_balanced_sum
#print axioms TheoremT.Continuum.so2PolynomialToCartesian_balanced_axis_coeff
#print axioms TheoremT.Continuum.so2_finite_radial_descent
