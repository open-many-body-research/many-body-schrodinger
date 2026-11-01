import GrushinScalarGridNormalization_v1
import GrushinScalarFixedGapRecurrence_v1
import GrushinScalarFixedGapBound_v1

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
#check @TheoremT.Continuum.grushinGridNorm
#check @TheoremT.Continuum.grushin_grid_time_bounds
#check @TheoremT.Continuum.grushin_gridNorm_nonneg
#check @TheoremT.Continuum.grushin_gridNorm_base
#check @TheoremT.Continuum.grushin_grid_lower_norm_le
#check @TheoremT.Continuum.grushin_inverse_gap_term_le
#check @TheoremT.Continuum.grushin_scaled_source_le
#check @TheoremT.Continuum.grushin_scaled_factorial_term_le
#check @TheoremT.Continuum.GrushinScalarFixedGapRecurrence
#check @TheoremT.Continuum.grushin_grid_recurrence_from_fixed_gap
#check @TheoremT.Continuum.grushin_scalar_fixed_gap_grid_bound
#check @TheoremT.Continuum.grushin_scalar_fixed_gap_bound
#check @TheoremT.Continuum.grushin_scalar_fixed_gap_zero

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.grushinGridNorm
#print axioms TheoremT.Continuum.grushin_grid_time_bounds
#print axioms TheoremT.Continuum.grushin_gridNorm_nonneg
#print axioms TheoremT.Continuum.grushin_gridNorm_base
#print axioms TheoremT.Continuum.grushin_grid_lower_norm_le
#print axioms TheoremT.Continuum.grushin_inverse_gap_term_le
#print axioms TheoremT.Continuum.grushin_scaled_source_le
#print axioms TheoremT.Continuum.grushin_scaled_factorial_term_le
#print axioms TheoremT.Continuum.GrushinScalarFixedGapRecurrence
#print axioms TheoremT.Continuum.grushin_grid_recurrence_from_fixed_gap
#print axioms TheoremT.Continuum.grushin_scalar_fixed_gap_grid_bound
#print axioms TheoremT.Continuum.grushin_scalar_fixed_gap_bound
#print axioms TheoremT.Continuum.grushin_scalar_fixed_gap_zero
