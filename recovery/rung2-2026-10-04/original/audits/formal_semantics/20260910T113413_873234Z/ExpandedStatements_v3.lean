import NuclearKSLift_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.NuclearKSSpace
#check @TheoremT.Continuum.nuclearKSLift
#check @TheoremT.Continuum.nuclearKSLift_contDiff
#check @TheoremT.Continuum.nuclearKSLift_locallyLipschitz
#check @TheoremT.Continuum.nuclearKSLift_selected_position
#check @TheoremT.Continuum.nuclearKSLift_nuclear_radius

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.NuclearKSSpace
#print axioms TheoremT.Continuum.nuclearKSLift
#print axioms TheoremT.Continuum.nuclearKSLift_contDiff
#print axioms TheoremT.Continuum.nuclearKSLift_locallyLipschitz
#print axioms TheoremT.Continuum.nuclearKSLift_selected_position
#print axioms TheoremT.Continuum.nuclearKSLift_nuclear_radius
