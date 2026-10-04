import LocalWeakYLaplacianDifferentiate_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.splitGrushin_zero_directional_commute
#check @TheoremT.Continuum.WeakGrushin.local_weak_y_laplacian_differentiate

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.splitGrushin_zero_directional_commute
#print axioms TheoremT.Continuum.WeakGrushin.local_weak_y_laplacian_differentiate
