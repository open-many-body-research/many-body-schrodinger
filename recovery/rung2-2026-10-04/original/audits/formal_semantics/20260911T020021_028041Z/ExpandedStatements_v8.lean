import KSRealPolynomialDescent_v1

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
#check @TheoremT.Continuum.ksRealPolynomialDescentA
#check @TheoremT.Continuum.ksRealPolynomialDescentB
#check @TheoremT.Continuum.ks_real_polynomial_physical_descent
#check @TheoremT.Continuum.ks_real_polynomial_descent_homogeneous
#check @TheoremT.Continuum.polynomialCoeffL1_real_descent_degree_bound
#check @TheoremT.Continuum.polynomialCoeffL1_real_descent_geometric_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksRealPolynomialDescentA
#print axioms TheoremT.Continuum.ksRealPolynomialDescentB
#print axioms TheoremT.Continuum.ks_real_polynomial_physical_descent
#print axioms TheoremT.Continuum.ks_real_polynomial_descent_homogeneous
#print axioms TheoremT.Continuum.polynomialCoeffL1_real_descent_degree_bound
#print axioms TheoremT.Continuum.polynomialCoeffL1_real_descent_geometric_bound
