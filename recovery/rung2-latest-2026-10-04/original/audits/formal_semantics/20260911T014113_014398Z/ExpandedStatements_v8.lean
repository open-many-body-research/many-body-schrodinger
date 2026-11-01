import HomogeneousPolynomialCoefficientL1Bound_v1

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
#check @TheoremT.Continuum.homogeneous_support_subset_degree_exponents
#check @TheoremT.Continuum.homogeneous_support_card_le_four_pow
#check @TheoremT.Continuum.homogeneous_polynomialCoeffL1_coefficient_bound
#check @TheoremT.Continuum.homogeneous_polynomialCoeffL1_geometric_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.homogeneous_support_subset_degree_exponents
#print axioms TheoremT.Continuum.homogeneous_support_card_le_four_pow
#print axioms TheoremT.Continuum.homogeneous_polynomialCoeffL1_coefficient_bound
#print axioms TheoremT.Continuum.homogeneous_polynomialCoeffL1_geometric_bound
