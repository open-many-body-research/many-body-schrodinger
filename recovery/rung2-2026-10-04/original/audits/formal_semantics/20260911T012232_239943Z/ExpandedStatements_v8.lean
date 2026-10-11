import CoulombSpinPhysicalPointwise_v1
import TwoElectronGroundPhysicalPointwise_v1
import KSDescentSpinorAlgebra_v1

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
#check @TheoremT.Continuum.coulomb_spin_physical_pointwise_representative
#check @TheoremT.Continuum.twoElectron_physical_ground_pointwise
#check @TheoremT.Continuum.ksSpinor
#check @TheoremT.Continuum.ksDescentQuadratic
#check @TheoremT.Continuum.ksSpinor_balanced_quadratic
#check @TheoremT.Continuum.ksDescentQuadratic_determinant
#check @TheoremT.Continuum.ksMap_radial_relation
#check @TheoremT.Continuum.ksCircleAction
#check @TheoremT.Continuum.ksMap_circle_action
#check @TheoremT.Continuum.ksMap_circle_invariant
#check @TheoremT.Continuum.ksMap_rotation_invariant
#check @TheoremT.Continuum.ksSpinor_circle_action
#check @TheoremT.Continuum.ks_pullback_circle_invariant

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.coulomb_spin_physical_pointwise_representative
#print axioms TheoremT.Continuum.twoElectron_physical_ground_pointwise
#print axioms TheoremT.Continuum.ksSpinor
#print axioms TheoremT.Continuum.ksDescentQuadratic
#print axioms TheoremT.Continuum.ksSpinor_balanced_quadratic
#print axioms TheoremT.Continuum.ksDescentQuadratic_determinant
#print axioms TheoremT.Continuum.ksMap_radial_relation
#print axioms TheoremT.Continuum.ksCircleAction
#print axioms TheoremT.Continuum.ksMap_circle_action
#print axioms TheoremT.Continuum.ksMap_circle_invariant
#print axioms TheoremT.Continuum.ksMap_rotation_invariant
#print axioms TheoremT.Continuum.ksSpinor_circle_action
#print axioms TheoremT.Continuum.ks_pullback_circle_invariant
