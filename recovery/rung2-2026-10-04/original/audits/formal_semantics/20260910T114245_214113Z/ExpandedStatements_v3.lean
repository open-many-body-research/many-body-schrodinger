import KSHoleCutoff_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksCutoffBase
#check @TheoremT.Continuum.ksHole
#check @TheoremT.Continuum.ksHole_contDiff
#check @TheoremT.Continuum.ksHole_nonneg
#check @TheoremT.Continuum.ksHole_le_one
#check @TheoremT.Continuum.ksHole_zero_on_inner
#check @TheoremT.Continuum.ksHole_one_on_outer
#check @TheoremT.Continuum.ksHole_test_tsupport_away

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksCutoffBase
#print axioms TheoremT.Continuum.ksHole
#print axioms TheoremT.Continuum.ksHole_contDiff
#print axioms TheoremT.Continuum.ksHole_nonneg
#print axioms TheoremT.Continuum.ksHole_le_one
#print axioms TheoremT.Continuum.ksHole_zero_on_inner
#print axioms TheoremT.Continuum.ksHole_one_on_outer
#print axioms TheoremT.Continuum.ksHole_test_tsupport_away
