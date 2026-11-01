import KSBalancedMonomialPairingSize_v1
import KSBalancedDescentPolynomial_v1

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
#check @TheoremT.Continuum.ksBalancedMonomialPairing_total
#check @TheoremT.Continuum.ksBalancedMonomialPairing_four_total
#check @TheoremT.Continuum.ksBalancedMonomialPairing_entry_le_total
#check @TheoremT.Continuum.ksDescentQuadraticPolynomial
#check @TheoremT.Continuum.ksDescentQuadraticPolynomial_homogeneous
#check @TheoremT.Continuum.ksDescentQuadraticPolynomial_eval
#check @TheoremT.Continuum.ksBalancedDescentPolynomial
#check @TheoremT.Continuum.ksBalancedDescentPolynomial_homogeneous
#check @TheoremT.Continuum.ksBalancedDescentPolynomial_eval
#check @TheoremT.Continuum.ksSpinor_balanced_descent_polynomial

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_total
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_four_total
#print axioms TheoremT.Continuum.ksBalancedMonomialPairing_entry_le_total
#print axioms TheoremT.Continuum.ksDescentQuadraticPolynomial
#print axioms TheoremT.Continuum.ksDescentQuadraticPolynomial_homogeneous
#print axioms TheoremT.Continuum.ksDescentQuadraticPolynomial_eval
#print axioms TheoremT.Continuum.ksBalancedDescentPolynomial
#print axioms TheoremT.Continuum.ksBalancedDescentPolynomial_homogeneous
#print axioms TheoremT.Continuum.ksBalancedDescentPolynomial_eval
#print axioms TheoremT.Continuum.ksSpinor_balanced_descent_polynomial
