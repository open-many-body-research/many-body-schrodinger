import KSRadialPolynomialHomogeneous_v1

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
#check @TheoremT.Continuum.ksRadialSquare_isHomogeneous
#check @TheoremT.Continuum.ksRadialMonomialCore_isHomogeneous
#check @TheoremT.Continuum.ks_radial_support_degree
#check @TheoremT.Continuum.ksRadialEven_isHomogeneous
#check @TheoremT.Continuum.ksRadialOdd_isHomogeneous
#check @TheoremT.Continuum.ksRadialOdd_eq_zero_of_degree_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksRadialSquare_isHomogeneous
#print axioms TheoremT.Continuum.ksRadialMonomialCore_isHomogeneous
#print axioms TheoremT.Continuum.ks_radial_support_degree
#print axioms TheoremT.Continuum.ksRadialEven_isHomogeneous
#print axioms TheoremT.Continuum.ksRadialOdd_isHomogeneous
#print axioms TheoremT.Continuum.ksRadialOdd_eq_zero_of_degree_zero
