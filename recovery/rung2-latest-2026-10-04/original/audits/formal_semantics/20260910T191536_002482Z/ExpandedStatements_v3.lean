import PairKSPotential_v1
import PairKSPotentialSmooth_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.pairKSPotential
#check @TheoremT.Continuum.pairKSCoefficientPatch
#check @TheoremT.Continuum.pairKSPotential_eq_coulomb_scaled
#check @TheoremT.Continuum.pairKSPotential_on_zero
#check @TheoremT.Continuum.pairKSCoefficientPatch_off_zero_collisionFree
#check @TheoremT.Continuum.pairKSPotential_contDiffAt
#check @TheoremT.Continuum.pairKSCoefficientPatch_isOpen

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.pairKSPotential
#print axioms TheoremT.Continuum.pairKSCoefficientPatch
#print axioms TheoremT.Continuum.pairKSPotential_eq_coulomb_scaled
#print axioms TheoremT.Continuum.pairKSPotential_on_zero
#print axioms TheoremT.Continuum.pairKSCoefficientPatch_off_zero_collisionFree
#print axioms TheoremT.Continuum.pairKSPotential_contDiffAt
#print axioms TheoremT.Continuum.pairKSCoefficientPatch_isOpen
