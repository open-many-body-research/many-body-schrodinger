import TensorBoxPointwiseFTC_v1

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
#check @TheoremT.Continuum.tensorClosedBox7
#check @TheoremT.Continuum.tensorClosedBox7_isClosed
#check @TheoremT.Continuum.tensorClosedBox7_update
#check @TheoremT.Continuum.tensorBoxNormField7
#check @TheoremT.Continuum.tensorBoxNormField7_measurable
#check @TheoremT.Continuum.tensorBoxNormField7_coordinate_average
#check @TheoremT.Continuum.tensor_box7_pointwise_integral_bound
#check @TheoremT.Continuum.tensor_box7_pointwise_uniform_average_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.tensorClosedBox7
#print axioms TheoremT.Continuum.tensorClosedBox7_isClosed
#print axioms TheoremT.Continuum.tensorClosedBox7_update
#print axioms TheoremT.Continuum.tensorBoxNormField7
#print axioms TheoremT.Continuum.tensorBoxNormField7_measurable
#print axioms TheoremT.Continuum.tensorBoxNormField7_coordinate_average
#print axioms TheoremT.Continuum.tensor_box7_pointwise_integral_bound
#print axioms TheoremT.Continuum.tensor_box7_pointwise_uniform_average_bound
