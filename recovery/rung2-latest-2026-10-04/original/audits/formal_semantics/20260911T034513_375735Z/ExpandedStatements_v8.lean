import PhysicalKSAnalyticAxisSlice_v1

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
#check @TheoremT.Continuum.physicalKSComplexAxisMap
#check @TheoremT.Continuum.physicalKSComplexAxisMapCLM
#check @TheoremT.Continuum.physicalKSComplexAxisMap_apply
#check @TheoremT.Continuum.physicalKSComplexAxisMap_block_norms
#check @TheoremT.Continuum.physicalKSAnalyticAxisRadius
#check @TheoremT.Continuum.physicalKSAnalyticAxisRadius_pos
#check @TheoremT.Continuum.physicalKSComplexAxisMap_quarter_bounds
#check @TheoremT.Continuum.physicalKSAnalyticDescent_axis_analytic_bounded

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.physicalKSComplexAxisMap
#print axioms TheoremT.Continuum.physicalKSComplexAxisMapCLM
#print axioms TheoremT.Continuum.physicalKSComplexAxisMap_apply
#print axioms TheoremT.Continuum.physicalKSComplexAxisMap_block_norms
#print axioms TheoremT.Continuum.physicalKSAnalyticAxisRadius
#print axioms TheoremT.Continuum.physicalKSAnalyticAxisRadius_pos
#print axioms TheoremT.Continuum.physicalKSComplexAxisMap_quarter_bounds
#print axioms TheoremT.Continuum.physicalKSAnalyticDescent_axis_analytic_bounded
