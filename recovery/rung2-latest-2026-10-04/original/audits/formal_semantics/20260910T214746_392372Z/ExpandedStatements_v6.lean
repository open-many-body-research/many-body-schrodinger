import ExpNegInvGlueExplicitBounds_v1
import SmoothTransitionExplicitBounds_v1

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
#check @TheoremT.Continuum.nonnegative_monomial_exp_neg_bound
#check @TheoremT.Continuum.expNegInvGlue_polynomial_bound
#check @TheoremT.Continuum.expNegInvGlue_deriv_formula
#check @TheoremT.Continuum.expNegInvGlue_second_deriv_formula
#check @TheoremT.Continuum.expNegInvGlue_deriv_abs_le_two
#check @TheoremT.Continuum.expNegInvGlue_second_deriv_abs_le_thirty_six
#check @TheoremT.Continuum.smoothTransition_denom_lower
#check @TheoremT.Continuum.smoothTransitionDenominator
#check @TheoremT.Continuum.smoothTransitionDenominator_contDiff
#check @TheoremT.Continuum.smoothTransitionDenominator_deriv
#check @TheoremT.Continuum.smoothTransitionDenominator_second_deriv
#check @TheoremT.Continuum.smoothTransitionDenominator_deriv_bounds
#check @TheoremT.Continuum.smoothTransition_denominator_product
#check @TheoremT.Continuum.smoothTransition_product_first
#check @TheoremT.Continuum.smoothTransition_product_second
#check @TheoremT.Continuum.smoothTransition_deriv_abs_le_ninety_six
#check @TheoremT.Continuum.smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.nonnegative_monomial_exp_neg_bound
#print axioms TheoremT.Continuum.expNegInvGlue_polynomial_bound
#print axioms TheoremT.Continuum.expNegInvGlue_deriv_formula
#print axioms TheoremT.Continuum.expNegInvGlue_second_deriv_formula
#print axioms TheoremT.Continuum.expNegInvGlue_deriv_abs_le_two
#print axioms TheoremT.Continuum.expNegInvGlue_second_deriv_abs_le_thirty_six
#print axioms TheoremT.Continuum.smoothTransition_denom_lower
#print axioms TheoremT.Continuum.smoothTransitionDenominator
#print axioms TheoremT.Continuum.smoothTransitionDenominator_contDiff
#print axioms TheoremT.Continuum.smoothTransitionDenominator_deriv
#print axioms TheoremT.Continuum.smoothTransitionDenominator_second_deriv
#print axioms TheoremT.Continuum.smoothTransitionDenominator_deriv_bounds
#print axioms TheoremT.Continuum.smoothTransition_denominator_product
#print axioms TheoremT.Continuum.smoothTransition_product_first
#print axioms TheoremT.Continuum.smoothTransition_product_second
#print axioms TheoremT.Continuum.smoothTransition_deriv_abs_le_ninety_six
#print axioms TheoremT.Continuum.smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
