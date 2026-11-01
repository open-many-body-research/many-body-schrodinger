import MvPolynomialCoefficientL1_v1
import MvPolynomialCoefficientL1Substitution_v1
import MvPolynomialCoefficientL1DegreeBound_v1

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
#check @TheoremT.Continuum.polynomialCoeffL1
#check @TheoremT.Continuum.polynomialCoeffL1_eq_sum
#check @TheoremT.Continuum.polynomialCoeffL1_nonneg
#check @TheoremT.Continuum.polynomialCoeffL1_eq_sum_of_support_subset
#check @TheoremT.Continuum.polynomialCoeffL1_zero
#check @TheoremT.Continuum.polynomialCoeffL1_monomial
#check @TheoremT.Continuum.polynomialCoeffL1_C
#check @TheoremT.Continuum.polynomialCoeffL1_one
#check @TheoremT.Continuum.polynomialCoeffL1_X
#check @TheoremT.Continuum.polynomialCoeffL1_add
#check @TheoremT.Continuum.polynomialCoeffL1_sum
#check @TheoremT.Continuum.polynomialCoeffL1_mul
#check @TheoremT.Continuum.polynomialCoeffL1_pow
#check @TheoremT.Continuum.polynomialCoeffL1_prod
#check @TheoremT.Continuum.polynomialCoeffL1_substitution_weighted
#check @TheoremT.Continuum.polynomialCoeffL1_substitution_nonexpansive
#check @TheoremT.Continuum.polynomialCoeffL1_coefficient_bound
#check @TheoremT.Continuum.polynomialCoeffL1_eq_zero_iff
#check @TheoremT.Continuum.polynomialCoeffL1_substitution_totalDegree
#check @TheoremT.Continuum.polynomialCoeffL1_substitution_degree_bound
#check @TheoremT.Continuum.polynomial_eval_norm_weighted
#check @TheoremT.Continuum.polynomial_eval_norm_le_coeffL1

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.polynomialCoeffL1
#print axioms TheoremT.Continuum.polynomialCoeffL1_eq_sum
#print axioms TheoremT.Continuum.polynomialCoeffL1_nonneg
#print axioms TheoremT.Continuum.polynomialCoeffL1_eq_sum_of_support_subset
#print axioms TheoremT.Continuum.polynomialCoeffL1_zero
#print axioms TheoremT.Continuum.polynomialCoeffL1_monomial
#print axioms TheoremT.Continuum.polynomialCoeffL1_C
#print axioms TheoremT.Continuum.polynomialCoeffL1_one
#print axioms TheoremT.Continuum.polynomialCoeffL1_X
#print axioms TheoremT.Continuum.polynomialCoeffL1_add
#print axioms TheoremT.Continuum.polynomialCoeffL1_sum
#print axioms TheoremT.Continuum.polynomialCoeffL1_mul
#print axioms TheoremT.Continuum.polynomialCoeffL1_pow
#print axioms TheoremT.Continuum.polynomialCoeffL1_prod
#print axioms TheoremT.Continuum.polynomialCoeffL1_substitution_weighted
#print axioms TheoremT.Continuum.polynomialCoeffL1_substitution_nonexpansive
#print axioms TheoremT.Continuum.polynomialCoeffL1_coefficient_bound
#print axioms TheoremT.Continuum.polynomialCoeffL1_eq_zero_iff
#print axioms TheoremT.Continuum.polynomialCoeffL1_substitution_totalDegree
#print axioms TheoremT.Continuum.polynomialCoeffL1_substitution_degree_bound
#print axioms TheoremT.Continuum.polynomial_eval_norm_weighted
#print axioms TheoremT.Continuum.polynomial_eval_norm_le_coeffL1
