import BoxEvaluationConstant_v1

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
#check @TheoremT.Continuum.boxEvaluationConstant
#check @TheoremT.Continuum.boxEvaluationConstant_pos
#check @TheoremT.Continuum.boxEvaluationConstant_eq_product
#check @TheoremT.Continuum.boxEvaluationConstant_four_three

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.boxEvaluationConstant
#print axioms TheoremT.Continuum.boxEvaluationConstant_pos
#print axioms TheoremT.Continuum.boxEvaluationConstant_eq_product
#print axioms TheoremT.Continuum.boxEvaluationConstant_four_three
