import KSTubeVolume_v1
import KSSingularSetNull_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksSpace_ball_volume
#check @TheoremT.Continuum.nuclear_KS_tube_volume
#check @TheoremT.Continuum.nuclear_KS_transverse_zero_null
#check @TheoremT.Continuum.nuclear_KS_selected_collision_null

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksSpace_ball_volume
#print axioms TheoremT.Continuum.nuclear_KS_tube_volume
#print axioms TheoremT.Continuum.nuclear_KS_transverse_zero_null
#print axioms TheoremT.Continuum.nuclear_KS_selected_collision_null
