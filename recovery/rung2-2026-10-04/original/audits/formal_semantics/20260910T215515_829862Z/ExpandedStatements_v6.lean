import FiniteFactorialMajorant_v1

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
#check @TheoremT.Continuum.finiteFactorialC
#check @TheoremT.Continuum.finiteFactorialA
#check @TheoremT.Continuum.finiteFactorialC_empty
#check @TheoremT.Continuum.finiteFactorialA_empty
#check @TheoremT.Continuum.finiteFactorialC_ge_one
#check @TheoremT.Continuum.finiteFactorialA_ge_one
#check @TheoremT.Continuum.le_finiteFactorialC
#check @TheoremT.Continuum.le_finiteFactorialA
#check @TheoremT.Continuum.finite_factorial_majorant
#check @TheoremT.Continuum.finite_factorial_common_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.finiteFactorialC
#print axioms TheoremT.Continuum.finiteFactorialA
#print axioms TheoremT.Continuum.finiteFactorialC_empty
#print axioms TheoremT.Continuum.finiteFactorialA_empty
#print axioms TheoremT.Continuum.finiteFactorialC_ge_one
#print axioms TheoremT.Continuum.finiteFactorialA_ge_one
#print axioms TheoremT.Continuum.le_finiteFactorialC
#print axioms TheoremT.Continuum.le_finiteFactorialA
#print axioms TheoremT.Continuum.finite_factorial_majorant
#print axioms TheoremT.Continuum.finite_factorial_common_bound
