import ProductSevenPullbackL2Budget_v2

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
#check @TheoremT.Continuum.seven_coordinate_restricted_volume
#check @TheoremT.Continuum.seven_coordinate_integral_image
#check @TheoremT.Continuum.seven_coordinate_pullback_memLp
#check @TheoremT.Continuum.seven_coordinate_integral_sq_le
#check @TheoremT.Continuum.seven_coordinate_sqrt_integral_le_eLpNorm
#check @TheoremT.Continuum.seven_coordinate_regionL2Budget
#check @TheoremT.Continuum.seven_coordinate_regionL2Budget_sq

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.seven_coordinate_restricted_volume
#print axioms TheoremT.Continuum.seven_coordinate_integral_image
#print axioms TheoremT.Continuum.seven_coordinate_pullback_memLp
#print axioms TheoremT.Continuum.seven_coordinate_integral_sq_le
#print axioms TheoremT.Continuum.seven_coordinate_sqrt_integral_le_eLpNorm
#print axioms TheoremT.Continuum.seven_coordinate_regionL2Budget
#print axioms TheoremT.Continuum.seven_coordinate_regionL2Budget_sq
