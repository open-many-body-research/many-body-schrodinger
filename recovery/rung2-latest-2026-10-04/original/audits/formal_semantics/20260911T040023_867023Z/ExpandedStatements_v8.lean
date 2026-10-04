import PhysicalKSAxisAnalyticDescent_v1

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
#check @TheoremT.Continuum.physicalKSAxisDescendedA
#check @TheoremT.Continuum.physicalKSAxisDescendedB
#check @TheoremT.Continuum.PhysicalKSAxisAnalyticDescentData
#check @TheoremT.Continuum.physicalKSAxisAnalyticDescent_data
#check @TheoremT.Continuum.nuclearKSPhysicalAxisAnalyticDescent_data
#check @TheoremT.Continuum.pairKSPhysicalAxisAnalyticDescent_data

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSAxisDescendedA
#print axioms TheoremT.Continuum.physicalKSAxisDescendedB
#print axioms TheoremT.Continuum.PhysicalKSAxisAnalyticDescentData
#print axioms TheoremT.Continuum.physicalKSAxisAnalyticDescent_data
#print axioms TheoremT.Continuum.nuclearKSPhysicalAxisAnalyticDescent_data
#print axioms TheoremT.Continuum.pairKSPhysicalAxisAnalyticDescent_data
