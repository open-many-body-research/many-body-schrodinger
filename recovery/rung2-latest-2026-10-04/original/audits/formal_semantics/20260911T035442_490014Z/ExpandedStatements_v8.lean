import NuclearDistanceAxisMap_v1

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
#check @TheoremT.Continuum.nuclearDistanceAxisZ
#check @TheoremT.Continuum.nuclearDistanceAxisW
#check @TheoremT.Continuum.nuclearDistanceAxisMap
#check @TheoremT.Continuum.nuclearDistanceAxisZ_analyticAt
#check @TheoremT.Continuum.nuclearDistanceAxisW_analyticAt
#check @TheoremT.Continuum.nuclearDistanceAxisMap_analyticOnNhd
#check @TheoremT.Continuum.nuclearDistanceAxisMap_center
#check @TheoremT.Continuum.nuclearDistanceAxis_bounds_closed
#check @TheoremT.Continuum.nuclearDistanceAxis_bounds

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclearDistanceAxisZ
#print axioms TheoremT.Continuum.nuclearDistanceAxisW
#print axioms TheoremT.Continuum.nuclearDistanceAxisMap
#print axioms TheoremT.Continuum.nuclearDistanceAxisZ_analyticAt
#print axioms TheoremT.Continuum.nuclearDistanceAxisW_analyticAt
#print axioms TheoremT.Continuum.nuclearDistanceAxisMap_analyticOnNhd
#print axioms TheoremT.Continuum.nuclearDistanceAxisMap_center
#print axioms TheoremT.Continuum.nuclearDistanceAxis_bounds_closed
#print axioms TheoremT.Continuum.nuclearDistanceAxis_bounds
