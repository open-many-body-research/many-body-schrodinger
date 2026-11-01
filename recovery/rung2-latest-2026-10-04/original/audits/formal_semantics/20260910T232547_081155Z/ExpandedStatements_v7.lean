import LocalWeakYToGrushinEquation_v1
import ProductDirectionalWordCommutator_v1

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
#check @TheoremT.Continuum.WeakGrushin.local_y_to_grushin_potential_equation
#check @TheoremT.Continuum.directionalWordCommutator
#check @TheoremT.Continuum.directionalWordProduct_eq_commutator_add
#check @TheoremT.Continuum.directionalWordCommutator_nil
#check @TheoremT.Continuum.directionalWordCommutator_locallyL2

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.local_y_to_grushin_potential_equation
#print axioms TheoremT.Continuum.directionalWordCommutator
#print axioms TheoremT.Continuum.directionalWordProduct_eq_commutator_add
#print axioms TheoremT.Continuum.directionalWordCommutator_nil
#print axioms TheoremT.Continuum.directionalWordCommutator_locallyL2
