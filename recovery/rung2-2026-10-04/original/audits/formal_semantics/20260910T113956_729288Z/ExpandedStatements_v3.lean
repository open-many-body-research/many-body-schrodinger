import KSTubeL2Mass_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.nuclear_KS_tube_squared_mass_le
#check @TheoremT.Continuum.scalar_coulomb_nuclear_KS_tube_squared_mass

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nuclear_KS_tube_squared_mass_le
#print axioms TheoremT.Continuum.scalar_coulomb_nuclear_KS_tube_squared_mass
