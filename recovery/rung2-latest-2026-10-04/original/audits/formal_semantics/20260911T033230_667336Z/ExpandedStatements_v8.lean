import PhysicalAxisRotation_v1

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
#check @TheoremT.Continuum.physicalAxisRotationLinear
#check @TheoremT.Continuum.physicalAxisRotationLinear_norm
#check @TheoremT.Continuum.physicalAxisRotationLinear_neg_apply
#check @TheoremT.Continuum.physicalAxisRotation
#check @TheoremT.Continuum.physicalAxisRotation_apply
#check @TheoremT.Continuum.physicalAxisRotation_apply_zero
#check @TheoremT.Continuum.physicalAxisRotation_apply_one
#check @TheoremT.Continuum.physicalAxisRotation_apply_two
#check @TheoremT.Continuum.physicalAxisRotation_axis

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalAxisRotationLinear
#print axioms TheoremT.Continuum.physicalAxisRotationLinear_norm
#print axioms TheoremT.Continuum.physicalAxisRotationLinear_neg_apply
#print axioms TheoremT.Continuum.physicalAxisRotation
#print axioms TheoremT.Continuum.physicalAxisRotation_apply
#print axioms TheoremT.Continuum.physicalAxisRotation_apply_zero
#print axioms TheoremT.Continuum.physicalAxisRotation_apply_one
#print axioms TheoremT.Continuum.physicalAxisRotation_apply_two
#print axioms TheoremT.Continuum.physicalAxisRotation_axis
