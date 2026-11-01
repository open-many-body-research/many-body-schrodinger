import KSSpinorPolynomialLocalInvariance_v1

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
#check @TheoremT.Continuum.ksSpace_norm_lt_of_coordinate_box
#check @TheoremT.Continuum.ksPolynomial_eq_of_spinor_real_ball_eval_eq
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_circle_invariant_of_local
#check @TheoremT.Continuum.ksRealPolynomialToSpinor_balanced_support_of_local

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksSpace_norm_lt_of_coordinate_box
#print axioms TheoremT.Continuum.ksPolynomial_eq_of_spinor_real_ball_eval_eq
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_circle_invariant_of_local
#print axioms TheoremT.Continuum.ksRealPolynomialToSpinor_balanced_support_of_local
