import HydrogenSpinGround_v1

/-! Exact full-spin hydrogen statements and axiom dependencies. Explicit
definitions expose the finite spin coefficients and actual spatial L2 data.
Only proof bodies and proof arguments are suppressed by pp.proofs. -/

namespace TheoremT.Continuum
set_option pp.proofs false
set_option pp.funBinderTypes true

#print hydrogenRadial
#print hydrogenRadialL2
#print oneElectronSpinMap
#print hydrogenSpinMap
#print one_electron_all_spin_fermionic
#print hydrogenSpinMap_injective
#print hydrogenSpinMap_two_independent
#print variational_ground_le_graph_eigenvalue
#print hydrogenRadialL2_eigenGraph
#print hydrogen_full_spin_ground
#print hydrogen_ground_energy_mem_spectrum
#print hydrogen_spectrum_lower_bound

#print axioms one_electron_all_spin_fermionic
#print axioms hydrogenSpinMap_injective
#print axioms hydrogenSpinMap_two_independent
#print axioms variational_ground_le_graph_eigenvalue
#print axioms hydrogenRadialL2_eigenGraph
#print axioms hydrogen_full_spin_ground
#print axioms hydrogen_ground_energy_mem_spectrum
#print axioms hydrogen_spectrum_lower_bound

end TheoremT.Continuum
