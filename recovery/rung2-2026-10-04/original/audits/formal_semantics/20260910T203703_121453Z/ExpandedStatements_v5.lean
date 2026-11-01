import PairKSLift_v1
import PairCoordinatesLaplacian_v1
import PairKSPrincipalIdentity_v1
import CoulombPairKSClassical_v1
import CoulombPairKSWeak_v1
import CoulombSpinPairKSWeak_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.PairKSSpace
#check @TheoremT.Continuum.pairSpectatorCoordinateEquiv
#check @TheoremT.Continuum.pairCenterEquiv
#check @TheoremT.Continuum.pairCenterEquiv_apply
#check @TheoremT.Continuum.pairCenterEquiv_basis
#check @TheoremT.Continuum.pairCenterEquiv_measurePreserving
#check @TheoremT.Continuum.pairCoordinatesLinear
#check @TheoremT.Continuum.pairCoordinates
#check @TheoremT.Continuum.pairCoordinates_first
#check @TheoremT.Continuum.pairCoordinates_second
#check @TheoremT.Continuum.pairCoordinates_first_basis
#check @TheoremT.Continuum.pairCoordinates_spectator_basis
#check @TheoremT.Continuum.pairKSLift
#check @TheoremT.Continuum.pairKSLift_contDiff
#check @TheoremT.Continuum.pairKSLift_locallyLipschitz
#check @TheoremT.Continuum.pairKSLift_first
#check @TheoremT.Continuum.pairKSLift_second
#check @TheoremT.Continuum.pairKSLift_difference
#check @TheoremT.Continuum.pairKSLift_pair_radius
#check @TheoremT.Continuum.pair_coordinates_bilinear_trace
#check @TheoremT.Continuum.pair_coordinates_weighted_laplacian
#check @TheoremT.Continuum.pair_KS_principal_identity
#check @TheoremT.Continuum.scalar_coulomb_pair_KS_classical_equation
#check @TheoremT.Continuum.scalar_coulomb_pair_KS_classical_pullback
#check @TheoremT.Continuum.scalar_coulomb_pair_KS_off_zero_weak
#check @TheoremT.Continuum.scalar_coulomb_pair_KS_weak
#check @TheoremT.Continuum.scalar_coulomb_pair_KS_weak_pullback
#check @TheoremT.Continuum.coulomb_spin_pair_KS_weak_representative

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.PairKSSpace
#print axioms TheoremT.Continuum.pairSpectatorCoordinateEquiv
#print axioms TheoremT.Continuum.pairCenterEquiv
#print axioms TheoremT.Continuum.pairCenterEquiv_apply
#print axioms TheoremT.Continuum.pairCenterEquiv_basis
#print axioms TheoremT.Continuum.pairCenterEquiv_measurePreserving
#print axioms TheoremT.Continuum.pairCoordinatesLinear
#print axioms TheoremT.Continuum.pairCoordinates
#print axioms TheoremT.Continuum.pairCoordinates_first
#print axioms TheoremT.Continuum.pairCoordinates_second
#print axioms TheoremT.Continuum.pairCoordinates_first_basis
#print axioms TheoremT.Continuum.pairCoordinates_spectator_basis
#print axioms TheoremT.Continuum.pairKSLift
#print axioms TheoremT.Continuum.pairKSLift_contDiff
#print axioms TheoremT.Continuum.pairKSLift_locallyLipschitz
#print axioms TheoremT.Continuum.pairKSLift_first
#print axioms TheoremT.Continuum.pairKSLift_second
#print axioms TheoremT.Continuum.pairKSLift_difference
#print axioms TheoremT.Continuum.pairKSLift_pair_radius
#print axioms TheoremT.Continuum.pair_coordinates_bilinear_trace
#print axioms TheoremT.Continuum.pair_coordinates_weighted_laplacian
#print axioms TheoremT.Continuum.pair_KS_principal_identity
#print axioms TheoremT.Continuum.scalar_coulomb_pair_KS_classical_equation
#print axioms TheoremT.Continuum.scalar_coulomb_pair_KS_classical_pullback
#print axioms TheoremT.Continuum.scalar_coulomb_pair_KS_off_zero_weak
#print axioms TheoremT.Continuum.scalar_coulomb_pair_KS_weak
#print axioms TheoremT.Continuum.scalar_coulomb_pair_KS_weak_pullback
#print axioms TheoremT.Continuum.coulomb_spin_pair_KS_weak_representative
