import SO2SpectatorRetainedRadius_v1

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
#check @TheoremT.Continuum.so2SpectatorFamily_retained_coefficient_bound
#check @TheoremT.Continuum.geometric_rate_lt_one_of_lt_retained_radius
#check @TheoremT.Continuum.so2SpectatorFamily_hasSum_on_retained_polydisc

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.so2SpectatorFamily_retained_coefficient_bound
#print axioms TheoremT.Continuum.geometric_rate_lt_one_of_lt_retained_radius
#print axioms TheoremT.Continuum.so2SpectatorFamily_hasSum_on_retained_polydisc
