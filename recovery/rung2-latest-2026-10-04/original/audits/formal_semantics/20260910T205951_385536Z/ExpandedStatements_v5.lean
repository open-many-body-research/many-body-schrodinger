import GrushinFactorialCutoffData_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.factorialRectCutoff
#check @TheoremT.Continuum.WeakGrushin.factorialRectCutoff_geometry
#check @TheoremT.Continuum.WeakGrushin.factorialRectCutoff_derivative_bounds
#check @TheoremT.Continuum.WeakGrushin.factorialRectCutoff_y_lower_radius
#check @TheoremT.Continuum.WeakGrushin.factorialRectCutoff_uniform_data

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.factorialRectCutoff
#print axioms TheoremT.Continuum.WeakGrushin.factorialRectCutoff_geometry
#print axioms TheoremT.Continuum.WeakGrushin.factorialRectCutoff_derivative_bounds
#print axioms TheoremT.Continuum.WeakGrushin.factorialRectCutoff_y_lower_radius
#print axioms TheoremT.Continuum.WeakGrushin.factorialRectCutoff_uniform_data
