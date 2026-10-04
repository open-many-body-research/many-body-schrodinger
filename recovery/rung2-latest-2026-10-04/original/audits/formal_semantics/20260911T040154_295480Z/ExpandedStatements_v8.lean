import NuclearDistanceRealRepresentative_v1

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
#check @TheoremT.Continuum.nuclearDistanceRealZ
#check @TheoremT.Continuum.nuclearDistanceRealW
#check @TheoremT.Continuum.nuclearDistanceRealSpatial
#check @TheoremT.Continuum.nuclearDistanceRealSpectator
#check @TheoremT.Continuum.nuclearDistanceRealZ_complexification
#check @TheoremT.Continuum.nuclearDistanceRealW_complexification
#check @TheoremT.Continuum.nuclearDistanceReal_heron
#check @TheoremT.Continuum.nuclearDistanceRealW_nonneg
#check @TheoremT.Continuum.nuclearDistanceReal_shifted_square
#check @TheoremT.Continuum.nuclearDistanceRealSpatial_norm
#check @TheoremT.Continuum.nuclearDistanceRealSpectator_norm
#check @TheoremT.Continuum.nuclearDistanceReal_separation_norm
#check @TheoremT.Continuum.nuclearDistanceRealRepresentative_norms
#check @TheoremT.Continuum.nuclearDistanceRealRepresentative_configuration_norms

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclearDistanceRealZ
#print axioms TheoremT.Continuum.nuclearDistanceRealW
#print axioms TheoremT.Continuum.nuclearDistanceRealSpatial
#print axioms TheoremT.Continuum.nuclearDistanceRealSpectator
#print axioms TheoremT.Continuum.nuclearDistanceRealZ_complexification
#print axioms TheoremT.Continuum.nuclearDistanceRealW_complexification
#print axioms TheoremT.Continuum.nuclearDistanceReal_heron
#print axioms TheoremT.Continuum.nuclearDistanceRealW_nonneg
#print axioms TheoremT.Continuum.nuclearDistanceReal_shifted_square
#print axioms TheoremT.Continuum.nuclearDistanceRealSpatial_norm
#print axioms TheoremT.Continuum.nuclearDistanceRealSpectator_norm
#print axioms TheoremT.Continuum.nuclearDistanceReal_separation_norm
#print axioms TheoremT.Continuum.nuclearDistanceRealRepresentative_norms
#print axioms TheoremT.Continuum.nuclearDistanceRealRepresentative_configuration_norms
