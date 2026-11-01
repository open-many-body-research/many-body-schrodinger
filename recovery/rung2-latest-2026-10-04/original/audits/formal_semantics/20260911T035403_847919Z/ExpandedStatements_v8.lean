import SO2SpectatorCoefficientInvariance_v1
import SO2SpectatorSeriesInvariance_v1

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
#check @TheoremT.Continuum.so2JointRealRotationCLM
#check @TheoremT.Continuum.so2JointRealRotationCLM_apply
#check @TheoremT.Continuum.so2SpectatorEvaluationPolynomial
#check @TheoremT.Continuum.so2SpectatorEvaluationPolynomial_coeff
#check @TheoremT.Continuum.so2SpectatorEvaluationPolynomial_eval
#check @TheoremT.Continuum.so2SpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
#check @TheoremT.Continuum.so2SpectatorCoefficientPolynomial_rotation_invariant
#check @TheoremT.Continuum.so2SpectatorCoefficientPolynomial_balanced_support
#check @TheoremT.Continuum.so2SpectatorFamily_rotation_invariant_of_hasSum
#check @TheoremT.Continuum.so2SpectatorFamily_balanced_support_of_hasSum

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2JointRealRotationCLM
#print axioms TheoremT.Continuum.so2JointRealRotationCLM_apply
#print axioms TheoremT.Continuum.so2SpectatorEvaluationPolynomial
#print axioms TheoremT.Continuum.so2SpectatorEvaluationPolynomial_coeff
#print axioms TheoremT.Continuum.so2SpectatorEvaluationPolynomial_eval
#print axioms TheoremT.Continuum.so2SpectatorCoefficientPolynomial_eval_eq_of_real_spectator_eq
#print axioms TheoremT.Continuum.so2SpectatorCoefficientPolynomial_rotation_invariant
#print axioms TheoremT.Continuum.so2SpectatorCoefficientPolynomial_balanced_support
#print axioms TheoremT.Continuum.so2SpectatorFamily_rotation_invariant_of_hasSum
#print axioms TheoremT.Continuum.so2SpectatorFamily_balanced_support_of_hasSum
