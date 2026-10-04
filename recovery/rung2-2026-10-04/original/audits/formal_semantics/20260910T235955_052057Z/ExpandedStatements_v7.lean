import ProductLocalDiagonalWeakH2_v1
import WeakGrushinRawLocalCutoff_v1

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
#check @TheoremT.Continuum.ProductLocalWeakDirectional.second_same_test
#check @TheoremT.Continuum.product_local_weakH2_of_diagonal_jets
#check @TheoremT.Continuum.WeakGrushin.principal_ae_eq_of_raw_local_output
#check @TheoremT.Continuum.WeakGrushin.rawGrushinCutoffError_zero_off
#check @TheoremT.Continuum.WeakGrushin.raw_local_weakH2_grushin_cutoff

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.second_same_test
#print axioms TheoremT.Continuum.product_local_weakH2_of_diagonal_jets
#print axioms TheoremT.Continuum.WeakGrushin.principal_ae_eq_of_raw_local_output
#print axioms TheoremT.Continuum.WeakGrushin.rawGrushinCutoffError_zero_off
#print axioms TheoremT.Continuum.WeakGrushin.raw_local_weakH2_grushin_cutoff
