import HydrogenRadialLpAudit_v1
import HydrogenRadialBounds_v1
import HydrogenRadialNorm_v1

/-! Readable exact semantic statements supplementing the explicit-instance
print in HydrogenRadialLpAudit_v1. Only proof bodies are suppressed. -/

open MeasureTheory
namespace TheoremT.Continuum

set_option pp.proofs false
set_option pp.funBinderTypes true

#print hydrogen_radial_L2_expanded
#print hydrogenRadial
#print hydrogenRadialL2
#print hydrogenRadialL2_coe_ae
#print hydrogen_radial_first_coefficient_bound
#print hydrogen_radial_second_coefficient_bound
#print hydrogen_exp_regularized_le
#print hydrogen_regularized_first_coefficient_bound
#print hydrogen_regularized_second_coefficient_bound
#print integral_radial_exp
#print hydrogenRadialL2_norm_sq

#print axioms hydrogen_radial_L2_expanded
#print axioms hydrogen_radial_first_coefficient_bound
#print axioms hydrogen_radial_second_coefficient_bound
#print axioms hydrogen_exp_regularized_le
#print axioms hydrogen_regularized_first_coefficient_bound
#print axioms hydrogen_regularized_second_coefficient_bound
#print axioms integral_radial_exp
#print axioms hydrogenRadialL2_norm_sq

end TheoremT.Continuum
