import WeakFactorialJetIdentifications_v2

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
#check @TheoremT.Continuum.WeakGrushin.mixedMultiIndexWord_zero_pi
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_perm
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_single_y
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_single_t
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_double_y
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_mixed
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_double_t

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.mixedMultiIndexWord_zero_pi
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_perm
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_single_y
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_single_t
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_double_y
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_mixed
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_double_t
