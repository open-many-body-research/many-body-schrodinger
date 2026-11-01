import PhysicalComplexAxisSlice_v1

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
#check @TheoremT.Continuum.physicalComplexAxisSlice
#check @TheoremT.Continuum.physicalComplexAxisSliceCLM
#check @TheoremT.Continuum.physicalComplexAxisSliceCLM_apply
#check @TheoremT.Continuum.physicalComplexAxisSlice_left
#check @TheoremT.Continuum.physicalComplexAxisSlice_right
#check @TheoremT.Continuum.physicalComplexAxisSlice_right_norm
#check @TheoremT.Continuum.physicalComplexAxisSlice_norm
#check @TheoremT.Continuum.physicalComplexAxisSlice_domain_iff

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalComplexAxisSlice
#print axioms TheoremT.Continuum.physicalComplexAxisSliceCLM
#print axioms TheoremT.Continuum.physicalComplexAxisSliceCLM_apply
#print axioms TheoremT.Continuum.physicalComplexAxisSlice_left
#print axioms TheoremT.Continuum.physicalComplexAxisSlice_right
#print axioms TheoremT.Continuum.physicalComplexAxisSlice_right_norm
#print axioms TheoremT.Continuum.physicalComplexAxisSlice_norm
#print axioms TheoremT.Continuum.physicalComplexAxisSlice_domain_iff
