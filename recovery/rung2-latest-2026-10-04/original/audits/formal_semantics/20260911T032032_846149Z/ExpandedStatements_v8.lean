import PhysicalKSAnalyticDescentCompatibility_v1

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
#check @TheoremT.Continuum.physicalKSPhysicalSpectatorRadius
#check @TheoremT.Continuum.physicalKSPhysicalSpatialRadius
#check @TheoremT.Continuum.physicalKSPhysicalSpectatorRadius_pos
#check @TheoremT.Continuum.physicalKSPhysicalSpatialRadius_pos
#check @TheoremT.Continuum.physicalKSAnalyticDescent_same_function_compatible
#check @TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_compatible_centers
#check @TheoremT.Continuum.pairKSPhysicalAnalyticDescent_compatible_centers

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSPhysicalSpectatorRadius
#print axioms TheoremT.Continuum.physicalKSPhysicalSpatialRadius
#print axioms TheoremT.Continuum.physicalKSPhysicalSpectatorRadius_pos
#print axioms TheoremT.Continuum.physicalKSPhysicalSpatialRadius_pos
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_same_function_compatible
#print axioms TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_compatible_centers
#print axioms TheoremT.Continuum.pairKSPhysicalAnalyticDescent_compatible_centers
