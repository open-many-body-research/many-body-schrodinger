import KSSpectatorHomogeneousReconstruction_v1

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
#check @TheoremT.Continuum.ksSpectatorTailIndex
#check @TheoremT.Continuum.ksSpectatorDegreeIndices
#check @TheoremT.Continuum.ksSpectatorTailIndex_degree
#check @TheoremT.Continuum.ksSpectatorTailIndex_injective_on_degree
#check @TheoremT.Continuum.mem_ksSpectatorDegreeIndices_iff
#check @TheoremT.Continuum.ksSpectatorCoefficientPolynomial_eval_reconstruct_degree
#check @TheoremT.Continuum.ksSpectatorCoefficientPolynomial_grouped_reconstruct

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksSpectatorTailIndex
#print axioms TheoremT.Continuum.ksSpectatorDegreeIndices
#print axioms TheoremT.Continuum.ksSpectatorTailIndex_degree
#print axioms TheoremT.Continuum.ksSpectatorTailIndex_injective_on_degree
#print axioms TheoremT.Continuum.mem_ksSpectatorDegreeIndices_iff
#print axioms TheoremT.Continuum.ksSpectatorCoefficientPolynomial_eval_reconstruct_degree
#print axioms TheoremT.Continuum.ksSpectatorCoefficientPolynomial_grouped_reconstruct
