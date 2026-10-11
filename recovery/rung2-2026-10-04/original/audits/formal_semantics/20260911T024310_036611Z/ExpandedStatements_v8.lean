import KSBalancedOddPolynomial_v1
import PhysicalKSTaylorOddSpectator_v1

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
#check @TheoremT.Continuum.ksBalancedPolynomial_odd_eq_zero
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_injective
#check @TheoremT.Continuum.ksRealPolynomial_odd_eq_zero_of_balanced
#check @TheoremT.Continuum.nuclearKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero
#check @TheoremT.Continuum.pairKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksBalancedPolynomial_odd_eq_zero
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_injective
#print axioms TheoremT.Continuum.ksRealPolynomial_odd_eq_zero_of_balanced
#print axioms TheoremT.Continuum.nuclearKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero
#print axioms TheoremT.Continuum.pairKSPhysicalTaylorSpectatorCoefficient_odd_eq_zero
