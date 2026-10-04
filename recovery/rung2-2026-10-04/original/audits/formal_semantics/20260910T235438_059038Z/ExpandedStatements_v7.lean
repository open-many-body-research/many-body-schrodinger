import GrushinFactorialBaseIndices_v1

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
#check @TheoremT.Continuum.WeakGrushin.FactorialBaseIndex
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndex_coordinate_le_of_cost
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices_mem
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices_zero_mem
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices_nonempty
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices_mono
#check @TheoremT.Continuum.WeakGrushin.factorialBaseIndices_coordinate_le

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.FactorialBaseIndex
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndex_coordinate_le_of_cost
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices_mem
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices_zero_mem
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices_nonempty
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices_mono
#print axioms TheoremT.Continuum.WeakGrushin.factorialBaseIndices_coordinate_le
