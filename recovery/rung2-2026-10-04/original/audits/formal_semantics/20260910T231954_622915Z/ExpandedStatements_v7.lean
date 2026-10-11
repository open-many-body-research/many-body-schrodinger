import GrushinFactorialOuterCardinality_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialDegreeTwoIndices
#check @TheoremT.Continuum.WeakGrushin.factorialDegreeTwoIndices_mem
#check @TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration
#check @TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration_eq
#check @TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration_card
#check @TheoremT.Continuum.WeakGrushin.factorialOuterIndices_card

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialDegreeTwoIndices
#print axioms TheoremT.Continuum.WeakGrushin.factorialDegreeTwoIndices_mem
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration_eq
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterDegreeEnumeration_card
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterIndices_card
