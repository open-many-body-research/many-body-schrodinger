import GrushinFactorialMonomialBound_v1
import GrushinFactorialOuterAssembly_v1

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
#check @TheoremT.Continuum.WeakGrushin.factorialOuterRadialOrder
#check @TheoremT.Continuum.WeakGrushin.factorialYMonomial_continuous
#check @TheoremT.Continuum.WeakGrushin.factorialYMonomial_abs_le
#check @TheoremT.Continuum.WeakGrushin.factorialYMonomial_radial_bound
#check @TheoremT.Continuum.WeakGrushin.factorialOuterRadialOrder_le
#check @TheoremT.Continuum.WeakGrushin.factorial_outer_monomial_bound
#check @TheoremT.Continuum.WeakGrushin.factorial_outer_component_L2
#check @TheoremT.Continuum.WeakGrushin.factorial_outer_L2_assembly

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterRadialOrder
#print axioms TheoremT.Continuum.WeakGrushin.factorialYMonomial_continuous
#print axioms TheoremT.Continuum.WeakGrushin.factorialYMonomial_abs_le
#print axioms TheoremT.Continuum.WeakGrushin.factorialYMonomial_radial_bound
#print axioms TheoremT.Continuum.WeakGrushin.factorialOuterRadialOrder_le
#print axioms TheoremT.Continuum.WeakGrushin.factorial_outer_monomial_bound
#print axioms TheoremT.Continuum.WeakGrushin.factorial_outer_component_L2
#print axioms TheoremT.Continuum.WeakGrushin.factorial_outer_L2_assembly
