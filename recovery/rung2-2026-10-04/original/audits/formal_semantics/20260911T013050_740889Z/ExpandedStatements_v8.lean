import KSRadialCoefficientL1_v1
import KSRadialCoefficientCoarseBound_v1

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
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadialSquare
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadialMonomialCore
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_weighted
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_totalDegree
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_degree_bound
#check @TheoremT.Continuum.three_pow_half_le_two_pow
#check @TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_coarse_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadialSquare
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadialMonomialCore
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_weighted
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_totalDegree
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_degree_bound
#print axioms TheoremT.Continuum.three_pow_half_le_two_pow
#print axioms TheoremT.Continuum.polynomialCoeffL1_ksRadial_combined_coarse_bound
