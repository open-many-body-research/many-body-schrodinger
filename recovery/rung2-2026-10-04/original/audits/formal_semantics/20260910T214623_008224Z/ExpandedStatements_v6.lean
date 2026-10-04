import FiniteWeakGrushinCoordinateRegularity_v1

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
#check @TheoremT.Continuum.WeakGrushin.MixedTriangularState.lower_order
#check @TheoremT.Continuum.WeakGrushin.ProductCoordinateWeakHk.restrict
#check @TheoremT.Continuum.WeakGrushin.finite_weak_grushin_coordinate_regularity

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.MixedTriangularState.lower_order
#print axioms TheoremT.Continuum.WeakGrushin.ProductCoordinateWeakHk.restrict
#print axioms TheoremT.Continuum.WeakGrushin.finite_weak_grushin_coordinate_regularity
