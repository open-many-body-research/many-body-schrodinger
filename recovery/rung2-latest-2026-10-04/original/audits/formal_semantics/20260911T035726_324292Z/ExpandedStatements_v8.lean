import NuclearDistanceAxisAlgebra_v1

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
#check @TheoremT.Continuum.nuclearDistanceAxisZ_mul
#check @TheoremT.Continuum.nuclearDistanceAxisW_add_Z_sq
#check @TheoremT.Continuum.nuclearDistanceAxisW_add_shifted_Z_sq

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclearDistanceAxisZ_mul
#print axioms TheoremT.Continuum.nuclearDistanceAxisW_add_Z_sq
#print axioms TheoremT.Continuum.nuclearDistanceAxisW_add_shifted_Z_sq
