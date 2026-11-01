import KSBalancedMonomialPairing_v1
import KSBalancedMonomialFactorization_v1
import KSPhysicalBalancedMonomial_v1

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
#check @TheoremT.Continuum.ksBalancedMonomialPairing
#check @TheoremT.Continuum.ksBalancedMonomialPairing_entries
#check @TheoremT.Continuum.ksBalancedMonomialPairing_margins
#check @TheoremT.Continuum.ksBalancedMonomialPairing_row_sum
#check @TheoremT.Continuum.ksBalancedMonomialPairing_column_sum
#check @TheoremT.Continuum.ksBalancedMonomialPairing_last_eq_remainder
#check @TheoremT.Continuum.ksBalancedMonomial_factorization
#check @TheoremT.Continuum.ksBalancedComplexMonomial_factorization
#check @TheoremT.Continuum.ksBalancedPolynomialMonomial_factorization
#check @TheoremT.Continuum.ksSpinor_balanced_monomial

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_entries
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_margins
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_row_sum
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_column_sum
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_last_eq_remainder
#print axioms TheoremT.Continuum.ksBalancedMonomial_factorization
#print axioms TheoremT.Continuum.ksBalancedComplexMonomial_factorization
#print axioms TheoremT.Continuum.ksBalancedPolynomialMonomial_factorization
#print axioms TheoremT.Continuum.ksSpinor_balanced_monomial
