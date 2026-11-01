import LocalProductDirectionalWeakUnique_v1
import LocalProductDirectionalWeakCompatibility_v1
import LocalWeakYLaplacianWordEquation_v1
import MixedTriangularExtension_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.productLocallyL2On_locallyIntegrableOn
#check @TheoremT.Continuum.ProductLocalWeakDirectional.unique
#check @TheoremT.Continuum.ProductLocalWeakDirectional.second_of_compatible_first
#check @TheoremT.Continuum.ProductLocalWeakDirectional.of_cutoff_plateau
#check @TheoremT.Continuum.WeakGrushin.local_weak_y_laplacian_word_equations
#check @TheoremT.Continuum.WeakGrushin.mixed_triangular_extend_two

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.productLocallyL2On_locallyIntegrableOn
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.unique
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.second_of_compatible_first
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.of_cutoff_plateau
#print axioms TheoremT.Continuum.WeakGrushin.local_weak_y_laplacian_word_equations
#print axioms TheoremT.Continuum.WeakGrushin.mixed_triangular_extend_two
