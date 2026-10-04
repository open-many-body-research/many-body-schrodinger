import PhysicalKSCoordinatesRotation_v1

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
#check @TheoremT.Continuum.position_nuclearKSPhysicalCoordinates
#check @TheoremT.Continuum.position_pairKSPhysicalCoordinates_zero
#check @TheoremT.Continuum.position_pairKSPhysicalCoordinates_one
#check @TheoremT.Continuum.configurationRotation_nuclearKSPhysicalCoordinates
#check @TheoremT.Continuum.configurationRotation_pairKSPhysicalCoordinates
#check @TheoremT.Continuum.originScaledDifference_configurationRotation
#check @TheoremT.Continuum.originScaledDifference_nuclearKSPhysicalCoordinates_rotation
#check @TheoremT.Continuum.originScaledDifference_pairKSPhysicalCoordinates_rotation

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.position_nuclearKSPhysicalCoordinates
#print axioms TheoremT.Continuum.position_pairKSPhysicalCoordinates_zero
#print axioms TheoremT.Continuum.position_pairKSPhysicalCoordinates_one
#print axioms TheoremT.Continuum.configurationRotation_nuclearKSPhysicalCoordinates
#print axioms TheoremT.Continuum.configurationRotation_pairKSPhysicalCoordinates
#print axioms TheoremT.Continuum.originScaledDifference_configurationRotation
#print axioms TheoremT.Continuum.originScaledDifference_nuclearKSPhysicalCoordinates_rotation
#print axioms TheoremT.Continuum.originScaledDifference_pairKSPhysicalCoordinates_rotation
