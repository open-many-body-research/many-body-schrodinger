import FiniteTensorMarginalBound_v1

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
#check @TheoremT.Continuum.TensorMarginal.tensor_lmarginal_add
#check @TheoremT.Continuum.TensorMarginal.tensor_lmarginal_const_mul
#check @TheoremT.Continuum.TensorMarginal.finite_tensor_marginal_bound
#check @TheoremT.Continuum.TensorMarginal.finite_tensor_product_bound
#check @TheoremT.Continuum.TensorMarginal.finiteTensorCoefficient
#check @TheoremT.Continuum.TensorMarginal.finite_tensor_uniform_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.TensorMarginal.tensor_lmarginal_add
#print axioms TheoremT.Continuum.TensorMarginal.tensor_lmarginal_const_mul
#print axioms TheoremT.Continuum.TensorMarginal.finite_tensor_marginal_bound
#print axioms TheoremT.Continuum.TensorMarginal.finite_tensor_product_bound
#print axioms TheoremT.Continuum.TensorMarginal.finiteTensorCoefficient
#print axioms TheoremT.Continuum.TensorMarginal.finite_tensor_uniform_bound
