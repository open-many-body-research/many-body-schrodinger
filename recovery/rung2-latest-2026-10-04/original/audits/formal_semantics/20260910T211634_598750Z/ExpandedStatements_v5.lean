import LocalWeakGrushinYEquation_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.local_spectator_invariant_weight_second_test
#check @TheoremT.Continuum.WeakGrushin.local_grushin_y_source_locallyL2
#check @TheoremT.Continuum.WeakGrushin.grushin_y_test_identity
#check @TheoremT.Continuum.WeakGrushin.local_grushin_to_y_equation

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.local_spectator_invariant_weight_second_test
#print axioms TheoremT.Continuum.WeakGrushin.local_grushin_y_source_locallyL2
#print axioms TheoremT.Continuum.WeakGrushin.grushin_y_test_identity
#print axioms TheoremT.Continuum.WeakGrushin.local_grushin_to_y_equation
