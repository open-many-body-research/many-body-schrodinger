import PhysicalKSAnalyticAxisRotation_v1

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
#check @TheoremT.Continuum.physicalKSAxisSymmetryRadius
#check @TheoremT.Continuum.physicalKSAxisSymmetryRadius_pos
#check @TheoremT.Continuum.physicalKSAnalyticDescent_axis_angle_invariant
#check @TheoremT.Continuum.real_unit_pair_exists_angle
#check @TheoremT.Continuum.physicalKSAnalyticDescent_axis_rotation_invariant

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSAxisSymmetryRadius
#print axioms TheoremT.Continuum.physicalKSAxisSymmetryRadius_pos
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_axis_angle_invariant
#print axioms TheoremT.Continuum.real_unit_pair_exists_angle
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_axis_rotation_invariant
