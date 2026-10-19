import KSRadialPolynomialReduction_v1

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
#check @TheoremT.Continuum.ksRadialSquare
#check @TheoremT.Continuum.ksRadialMonomialCore
#check @TheoremT.Continuum.ksRadialEven
#check @TheoremT.Continuum.ksRadialOdd
#check @TheoremT.Continuum.ks_radial_power_reduction
#check @TheoremT.Continuum.ksRadialMonomialCore_eval
#check @TheoremT.Continuum.ks_radial_polynomial_reduction

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksRadialSquare
#print axioms TheoremT.Continuum.ksRadialMonomialCore
#print axioms TheoremT.Continuum.ksRadialEven
#print axioms TheoremT.Continuum.ksRadialOdd
#print axioms TheoremT.Continuum.ks_radial_power_reduction
#print axioms TheoremT.Continuum.ksRadialMonomialCore_eval
#print axioms TheoremT.Continuum.ks_radial_polynomial_reduction
