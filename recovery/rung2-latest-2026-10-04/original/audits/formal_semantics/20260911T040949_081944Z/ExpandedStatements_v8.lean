import NuclearDistanceRealAxisDomain_v1

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
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput
#check @TheoremT.Continuum.nuclearDistanceRealSpectator_sub
#check @TheoremT.Continuum.nuclearDistanceRealSpectator_sub_norm
#check @TheoremT.Continuum.nuclearDistanceRealSpectator_add_increment
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput_complex_map
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput_spectator
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput_transverse_square
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput_domain
#check @TheoremT.Continuum.nuclearDistanceRealAxisInput_domain_of_triangle

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput
#print axioms TheoremT.Continuum.nuclearDistanceRealSpectator_sub
#print axioms TheoremT.Continuum.nuclearDistanceRealSpectator_sub_norm
#print axioms TheoremT.Continuum.nuclearDistanceRealSpectator_add_increment
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput_complex_map
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput_spectator
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput_transverse_square
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput_domain
#print axioms TheoremT.Continuum.nuclearDistanceRealAxisInput_domain_of_triangle
