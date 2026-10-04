import MixedYIterationBudget_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.mixedYSourceBudget
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationNext
#check @TheoremT.Continuum.WeakGrushin.mixedYSourceBudget_nonneg
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationNext_ge
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationNext_nonneg

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.mixedYSourceBudget
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationNext
#print axioms TheoremT.Continuum.WeakGrushin.mixedYSourceBudget_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationNext_ge
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationNext_nonneg
