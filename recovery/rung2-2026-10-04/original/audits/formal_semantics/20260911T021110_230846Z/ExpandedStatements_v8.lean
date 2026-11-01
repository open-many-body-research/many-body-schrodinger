import SpectatorGeometricMultiindexSum_v1

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
#check @TheoremT.Continuum.spectatorGeometricWeight
#check @TheoremT.Continuum.spectatorGeometricWeight_nonneg
#check @TheoremT.Continuum.spectator_geometric_hasSum
#check @TheoremT.Continuum.spectator_geometric_summable
#check @TheoremT.Continuum.spectator_geometric_tsum
#check @TheoremT.Continuum.spectator_geometric_tsum_uniform_bound
#check @TheoremT.Continuum.spectator_geometric_tsum_dimension_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spectatorGeometricWeight
#print axioms TheoremT.Continuum.spectatorGeometricWeight_nonneg
#print axioms TheoremT.Continuum.spectator_geometric_hasSum
#print axioms TheoremT.Continuum.spectator_geometric_summable
#print axioms TheoremT.Continuum.spectator_geometric_tsum
#print axioms TheoremT.Continuum.spectator_geometric_tsum_uniform_bound
#print axioms TheoremT.Continuum.spectator_geometric_tsum_dimension_zero
