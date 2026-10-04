import PhysicalKSAnalyticDescentSurjectivity_v1

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
#check @TheoremT.Continuum.nuclearKSPhysicalCoordinates
#check @TheoremT.Continuum.pairKSPhysicalCoordinates
#check @TheoremT.Continuum.PhysicalKSAnalyticDescentOnPhysicalNeighborhood
#check @TheoremT.Continuum.physicalKSAnalyticDescent_descend_surjective
#check @TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_physical_neighborhood
#check @TheoremT.Continuum.pairKSPhysicalAnalyticDescent_physical_neighborhood

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclearKSPhysicalCoordinates
#print axioms TheoremT.Continuum.pairKSPhysicalCoordinates
#print axioms TheoremT.Continuum.PhysicalKSAnalyticDescentOnPhysicalNeighborhood
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_descend_surjective
#print axioms TheoremT.Continuum.nuclearKSPhysicalAnalyticDescent_physical_neighborhood
#print axioms TheoremT.Continuum.pairKSPhysicalAnalyticDescent_physical_neighborhood
