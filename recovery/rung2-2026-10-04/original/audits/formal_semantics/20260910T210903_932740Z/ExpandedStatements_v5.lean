import ProductDirectionalWordLeibniz_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ProductLocalWeakDirectional.list_sum
#check @TheoremT.Continuum.productLocallyL2On_list_sum
#check @TheoremT.Continuum.directionalWordDeriv
#check @TheoremT.Continuum.directionalWordDeriv_contDiffOn
#check @TheoremT.Continuum.directionalWordProduct
#check @TheoremT.Continuum.directionalWordProduct_nil
#check @TheoremT.Continuum.directionalWordProduct_cons
#check @TheoremT.Continuum.directionalWordProduct_locallyL2
#check @TheoremT.Continuum.directionalWordProduct_localD

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.list_sum
#print axioms TheoremT.Continuum.productLocallyL2On_list_sum
#print axioms TheoremT.Continuum.directionalWordDeriv
#print axioms TheoremT.Continuum.directionalWordDeriv_contDiffOn
#print axioms TheoremT.Continuum.directionalWordProduct
#print axioms TheoremT.Continuum.directionalWordProduct_nil
#print axioms TheoremT.Continuum.directionalWordProduct_cons
#print axioms TheoremT.Continuum.directionalWordProduct_locallyL2
#print axioms TheoremT.Continuum.directionalWordProduct_localD
