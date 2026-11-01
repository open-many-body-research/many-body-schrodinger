import KSMapHessian_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksJacobian_bilinear_symmetry
#check @TheoremT.Continuum.ksMap_coordinate_second_fderiv
#check @TheoremT.Continuum.ksBasis
#check @TheoremT.Continuum.ksMap_coordinate_laplacian_zero
#check @TheoremT.Continuum.ksMap_fderiv_coordinate

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksJacobian_bilinear_symmetry
#print axioms TheoremT.Continuum.ksMap_coordinate_second_fderiv
#print axioms TheoremT.Continuum.ksBasis
#print axioms TheoremT.Continuum.ksMap_coordinate_laplacian_zero
#print axioms TheoremT.Continuum.ksMap_fderiv_coordinate
