import MixedYIterationBudgetSequence_v1
import MixedYFiniteIteration_v1
import MixedYFiveStepReserve_v1
import MixedYIterationBudgetScale_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_nonneg
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_le_succ
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_monotone
#check @TheoremT.Continuum.WeakGrushin.mixedTriangularState_potential_iterate
#check @TheoremT.Continuum.WeakGrushin.spectatorFiniteState_five_y_steps
#check @TheoremT.Continuum.WeakGrushin.mixedYSourceBudget_input_mono
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationNext_input_mono
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationNext_scale
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_scale
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_input_mono
#check @TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_common_bound

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_nonneg
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_le_succ
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_monotone
#print axioms TheoremT.Continuum.WeakGrushin.mixedTriangularState_potential_iterate
#print axioms TheoremT.Continuum.WeakGrushin.spectatorFiniteState_five_y_steps
#print axioms TheoremT.Continuum.WeakGrushin.mixedYSourceBudget_input_mono
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationNext_input_mono
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationNext_scale
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_scale
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_input_mono
#print axioms TheoremT.Continuum.WeakGrushin.mixedYIterationBudgetSeq_common_bound
