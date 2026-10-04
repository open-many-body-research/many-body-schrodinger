import AllFiniteCoordinateRepresentativesGlue_v1
import ProductLocalWeakWordsQuantitativeRepresentative_v1

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
#check @TheoremT.Continuum.coordinate_words7_congr_on_open
#check @TheoremT.Continuum.all_finite_coordinate_representatives_glue
#check @TheoremT.Continuum.product_local_weak_words7_quantitative_representative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.coordinate_words7_congr_on_open
#print axioms TheoremT.Continuum.all_finite_coordinate_representatives_glue
#print axioms TheoremT.Continuum.product_local_weak_words7_quantitative_representative
