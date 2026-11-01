import WeakFactorialJet_v1

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
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_tendsto
#check @TheoremT.Continuum.WeakGrushin.weakCoordinateJet_ae_smooth
#check @TheoremT.Continuum.WeakGrushin.weakFactorialJet_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_tendsto
#print axioms TheoremT.Continuum.WeakGrushin.weakCoordinateJet_ae_smooth
#print axioms TheoremT.Continuum.WeakGrushin.weakFactorialJet_zero
