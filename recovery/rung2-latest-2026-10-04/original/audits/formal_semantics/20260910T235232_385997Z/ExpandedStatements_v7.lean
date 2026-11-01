import GrushinRecurrenceForcingAbsorption_v1
import GrushinLocalizedScalarAbsorption_v1
import NonnegativeEnergySlabBound_v1

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
#check @TheoremT.Continuum.grushinFactorialLossSum
#check @TheoremT.Continuum.grushin_choose_factorial_eq_ratio
#check @TheoremT.Continuum.grushin_choose_loss_sum_eq
#check @TheoremT.Continuum.grushin_factorial_loss_sum_nonneg
#check @TheoremT.Continuum.grushin_first_two_factorial_losses_le
#check @TheoremT.Continuum.grushin_principal_potential_absorption
#check @TheoremT.Continuum.grushinLocalizedCoefficient
#check @TheoremT.Continuum.grushin_localized_scalar_absorption
#check @TheoremT.Continuum.grushin_fixed_gap_recurrence_of_localized_bounds
#check @TheoremT.Continuum.nonnegative_energy_slab_bounds

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.grushinFactorialLossSum
#print axioms TheoremT.Continuum.grushin_choose_factorial_eq_ratio
#print axioms TheoremT.Continuum.grushin_choose_loss_sum_eq
#print axioms TheoremT.Continuum.grushin_factorial_loss_sum_nonneg
#print axioms TheoremT.Continuum.grushin_first_two_factorial_losses_le
#print axioms TheoremT.Continuum.grushin_principal_potential_absorption
#print axioms TheoremT.Continuum.grushinLocalizedCoefficient
#print axioms TheoremT.Continuum.grushin_localized_scalar_absorption
#print axioms TheoremT.Continuum.grushin_fixed_gap_recurrence_of_localized_bounds
#print axioms TheoremT.Continuum.nonnegative_energy_slab_bounds
