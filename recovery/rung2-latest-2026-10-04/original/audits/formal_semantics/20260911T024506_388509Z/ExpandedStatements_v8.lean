import MultiindexFactorialDimensionBound_v1

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
#check @TheoremT.Continuum.multinomial_univ_le_card_pow_sum
#check @TheoremT.Continuum.factorial_sum_le_card_pow_mul_prod_factorial
#check @TheoremT.Continuum.factorial_sum_le_card_pow_mul_prod_factorial_real

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.multinomial_univ_le_card_pow_sum
#print axioms TheoremT.Continuum.factorial_sum_le_card_pow_mul_prod_factorial
#print axioms TheoremT.Continuum.factorial_sum_le_card_pow_mul_prod_factorial_real
