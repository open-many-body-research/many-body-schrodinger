import KSHessianTraceContraction_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksTargetBasis
#check @TheoremT.Continuum.ksMap_fderiv_basis_expansion
#check @TheoremT.Continuum.ks_bilinear_trace_contraction

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksTargetBasis
#print axioms TheoremT.Continuum.ksMap_fderiv_basis_expansion
#print axioms TheoremT.Continuum.ks_bilinear_trace_contraction
