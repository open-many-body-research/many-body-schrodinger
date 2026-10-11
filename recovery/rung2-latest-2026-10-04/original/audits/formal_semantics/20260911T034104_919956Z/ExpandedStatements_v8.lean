import PhysicalRealAxisSliceBounds_v1

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
#check @TheoremT.Continuum.physicalRealAxisSpatial
#check @TheoremT.Continuum.physicalRealAxisSpectator
#check @TheoremT.Continuum.physicalRealAxis_complexification
#check @TheoremT.Continuum.physicalRealAxisSpectator_norm
#check @TheoremT.Continuum.physicalRealAxisSpatial_norm_sq
#check @TheoremT.Continuum.physicalRealAxisSpatial_norm_le
#check @TheoremT.Continuum.physicalRealAxis_domain_of_norm_lt

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalRealAxisSpatial
#print axioms TheoremT.Continuum.physicalRealAxisSpectator
#print axioms TheoremT.Continuum.physicalRealAxis_complexification
#print axioms TheoremT.Continuum.physicalRealAxisSpectator_norm
#print axioms TheoremT.Continuum.physicalRealAxisSpatial_norm_sq
#print axioms TheoremT.Continuum.physicalRealAxisSpatial_norm_le
#print axioms TheoremT.Continuum.physicalRealAxis_domain_of_norm_lt
