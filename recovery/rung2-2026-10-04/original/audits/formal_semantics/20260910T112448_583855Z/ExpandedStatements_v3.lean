import KSMapGeometry_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.KSSpace
#check @TheoremT.Continuum.ksMap
#check @TheoremT.Continuum.ksJacobian
#check @TheoremT.Continuum.ksMap_norm_sq
#check @TheoremT.Continuum.ksMap_norm
#check @TheoremT.Continuum.ksMap_eq_zero_iff
#check @TheoremT.Continuum.ksJacobian_row_orthogonality
#check @TheoremT.Continuum.ksMap_contDiff

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.KSSpace
#print axioms TheoremT.Continuum.ksMap
#print axioms TheoremT.Continuum.ksJacobian
#print axioms TheoremT.Continuum.ksMap_norm_sq
#print axioms TheoremT.Continuum.ksMap_norm
#print axioms TheoremT.Continuum.ksMap_eq_zero_iff
#print axioms TheoremT.Continuum.ksJacobian_row_orthogonality
#print axioms TheoremT.Continuum.ksMap_contDiff
