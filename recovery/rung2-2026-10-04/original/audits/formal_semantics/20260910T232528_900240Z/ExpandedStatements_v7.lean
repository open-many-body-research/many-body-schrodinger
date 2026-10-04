import SmoothFactorialJet_v1

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
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_contDiff
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_tsupport_subset
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_hasCompactSupport
#check @TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_perm
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_contDiff
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_tsupport_subset
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_hasCompactSupport
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_zero
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_add_single_y
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_add_single_t
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_single_y
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_single_t
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_double_y
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_mixed
#check @TheoremT.Continuum.WeakGrushin.smoothFactorialJet_double_t

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_contDiff
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_tsupport_subset
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_hasCompactSupport
#print axioms TheoremT.Continuum.WeakGrushin.complexDirectionalWordDeriv_perm
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_contDiff
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_tsupport_subset
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_hasCompactSupport
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_zero
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_add_single_y
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_add_single_t
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_single_y
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_single_t
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_double_y
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_mixed
#print axioms TheoremT.Continuum.WeakGrushin.smoothFactorialJet_double_t
