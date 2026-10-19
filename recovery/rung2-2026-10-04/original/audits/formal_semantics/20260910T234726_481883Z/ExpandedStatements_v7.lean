import WeakFactorialJetTests_v1
import WeakFactorialJetSupport_v1

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
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_directional
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_test_identity
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_tests_integrable
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_tests
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_eq_local_of_tests
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_closed_support
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_closed_support
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_eq_of_local_tests_support

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_directional
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_test_identity
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_tests_integrable
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_tests
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_eq_local_of_tests
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_closed_support
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_closed_support
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_ae_eq_of_local_tests_support
