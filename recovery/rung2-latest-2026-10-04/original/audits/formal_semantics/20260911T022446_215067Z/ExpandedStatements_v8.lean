import PhysicalKSComplexTaylorExtension_v1

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
#check @TheoremT.Continuum.physicalKSComplexTaylorExtension
#check @TheoremT.Continuum.physicalKSComplexTaylorExtension_analytic
#check @TheoremT.Continuum.physicalKSComplexTaylorExtension_norm_bound
#check @TheoremT.Continuum.physicalKSComplexTaylorExtension_agrees_on_real_ball

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSComplexTaylorExtension
#print axioms TheoremT.Continuum.physicalKSComplexTaylorExtension_analytic
#print axioms TheoremT.Continuum.physicalKSComplexTaylorExtension_norm_bound
#print axioms TheoremT.Continuum.physicalKSComplexTaylorExtension_agrees_on_real_ball
