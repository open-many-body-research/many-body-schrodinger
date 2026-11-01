import GrushinScaledFallingFactorial_v1

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
#check @TheoremT.Continuum.grushin_factorial_ratio_eq_descFactorial
#check @TheoremT.Continuum.grushin_normalization_scale_nonneg
#check @TheoremT.Continuum.grushin_normalization_scale_pos
#check @TheoremT.Continuum.grushin_normalization_scale_le_one
#check @TheoremT.Continuum.grushin_normalization_scale_bounds
#check @TheoremT.Continuum.grushin_scaled_falling_factorial_le_rho_pow
#check @TheoremT.Continuum.grushin_scaled_falling_factorial_le_one
#check @TheoremT.Continuum.grushin_scaled_factorial_le_one

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.grushin_factorial_ratio_eq_descFactorial
#print axioms TheoremT.Continuum.grushin_normalization_scale_nonneg
#print axioms TheoremT.Continuum.grushin_normalization_scale_pos
#print axioms TheoremT.Continuum.grushin_normalization_scale_le_one
#print axioms TheoremT.Continuum.grushin_normalization_scale_bounds
#print axioms TheoremT.Continuum.grushin_scaled_falling_factorial_le_rho_pow
#print axioms TheoremT.Continuum.grushin_scaled_falling_factorial_le_one
#print axioms TheoremT.Continuum.grushin_scaled_factorial_le_one
