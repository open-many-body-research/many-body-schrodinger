import PhysicalKSBoxFactorialBudgetMono_v1
import SpinOriginFactorialBudgets_v1

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
#check @TheoremT.Continuum.commonKSBoxFactorialConstant_one_le
#check @TheoremT.Continuum.PhysicalKSBoxFactorialData.mono_source_budget
#check @TheoremT.Continuum.complex_component_norm_le_sqrt_sum_sq
#check @TheoremT.Continuum.spinOriginFactorialSourceBudget
#check @TheoremT.Continuum.spinOriginFactorialSourceBudget_nonneg
#check @TheoremT.Continuum.spinOriginFactorialSourceBudget_component_le
#check @TheoremT.Continuum.spinOriginH12Budget_component_le
#check @TheoremT.Continuum.PhysicalKSBoxFactorialData.mono_spin_budget

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.commonKSBoxFactorialConstant_one_le
#print axioms TheoremT.Continuum.PhysicalKSBoxFactorialData.mono_source_budget
#print axioms TheoremT.Continuum.complex_component_norm_le_sqrt_sum_sq
#print axioms TheoremT.Continuum.spinOriginFactorialSourceBudget
#print axioms TheoremT.Continuum.spinOriginFactorialSourceBudget_nonneg
#print axioms TheoremT.Continuum.spinOriginFactorialSourceBudget_component_le
#print axioms TheoremT.Continuum.spinOriginH12Budget_component_le
#print axioms TheoremT.Continuum.PhysicalKSBoxFactorialData.mono_spin_budget
