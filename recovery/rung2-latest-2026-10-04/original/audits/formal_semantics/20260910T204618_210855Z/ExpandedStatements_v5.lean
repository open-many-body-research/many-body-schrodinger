import CoulombOriginScaling_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.collisionFree_real_smul
#check @TheoremT.Continuum.smoothLaplacian_comp_real_smul_at
#check @TheoremT.Continuum.scalar_coulomb_origin_scaled_classical_equation

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.collisionFree_real_smul
#print axioms TheoremT.Continuum.smoothLaplacian_comp_real_smul_at
#print axioms TheoremT.Continuum.scalar_coulomb_origin_scaled_classical_equation
