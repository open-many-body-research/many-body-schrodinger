import KSVectorLaplacian_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksMap_second_fderiv_coordinate
#check @TheoremT.Continuum.ksMap_vector_laplacian_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksMap_second_fderiv_coordinate
#print axioms TheoremT.Continuum.ksMap_vector_laplacian_zero
