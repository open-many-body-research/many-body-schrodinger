import KSHoleDerivatives_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksBasePartial
#check @TheoremT.Continuum.ksBasePartial_contDiff
#check @TheoremT.Continuum.ksBasePartial_compact
#check @TheoremT.Continuum.ksHole_partial
#check @TheoremT.Continuum.ksHole_secondPartial
#check @TheoremT.Continuum.ksHole_derivative_bound
#check @TheoremT.Continuum.ksHole_secondDerivative_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksBasePartial
#print axioms TheoremT.Continuum.ksBasePartial_contDiff
#print axioms TheoremT.Continuum.ksBasePartial_compact
#print axioms TheoremT.Continuum.ksHole_partial
#print axioms TheoremT.Continuum.ksHole_secondPartial
#print axioms TheoremT.Continuum.ksHole_derivative_bound
#print axioms TheoremT.Continuum.ksHole_secondDerivative_bound
