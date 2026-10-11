import ComplexPolynomialRealSlice_v2
import KSSpinorForwardPolynomial_v1
import KSSpinorPolynomialRealSlice_v1

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
#check @TheoremT.Continuum.complexPolynomial_eq_of_real_eval_eq
#check @TheoremT.Continuum.ksSpinorForwardPolynomial
#check @TheoremT.Continuum.ksSpinorPolynomialToReal
#check @TheoremT.Continuum.ksSpinorForwardPolynomial_physical_eval
#check @TheoremT.Continuum.ksSpinorPolynomialToReal_physical_eval
#check @TheoremT.Continuum.ksPolynomialCircleAction_physical_eval
#check @TheoremT.Continuum.ksSpinorForwardPolynomial_inverse
#check @TheoremT.Continuum.ksSpinorPolynomialToReal_left_inverse
#check @TheoremT.Continuum.ksSpinorPolynomialToReal_injective
#check @TheoremT.Continuum.ksPolynomial_eq_of_spinor_real_eval_eq
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_circle_invariant
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_balanced_support

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.complexPolynomial_eq_of_real_eval_eq
#print axioms TheoremT.Continuum.ksSpinorForwardPolynomial
#print axioms TheoremT.Continuum.ksSpinorPolynomialToReal
#print axioms TheoremT.Continuum.ksSpinorForwardPolynomial_physical_eval
#print axioms TheoremT.Continuum.ksSpinorPolynomialToReal_physical_eval
#print axioms TheoremT.Continuum.ksPolynomialCircleAction_physical_eval
#print axioms TheoremT.Continuum.ksSpinorForwardPolynomial_inverse
#print axioms TheoremT.Continuum.ksSpinorPolynomialToReal_left_inverse
#print axioms TheoremT.Continuum.ksSpinorPolynomialToReal_injective
#print axioms TheoremT.Continuum.ksPolynomial_eq_of_spinor_real_eval_eq
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_circle_invariant
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_balanced_support
