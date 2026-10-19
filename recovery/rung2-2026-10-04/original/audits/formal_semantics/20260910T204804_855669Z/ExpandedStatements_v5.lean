import EpsilonNuclearKSPotential_v1
import EpsilonPairKSPotential_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.epsilonNuclearKSPotential
#check @TheoremT.Continuum.nuclearKSPotential_energy_affine
#check @TheoremT.Continuum.epsilonNuclearKSPotential_energy_affine
#check @TheoremT.Continuum.epsilonNuclearKSPotential_eq_coulomb_scaled
#check @TheoremT.Continuum.epsilonNuclearKSPotential_on_zero
#check @TheoremT.Continuum.epsilonNuclearKSPotential_contDiffAt
#check @TheoremT.Continuum.epsilonPairKSPotential
#check @TheoremT.Continuum.pairKSPotential_energy_affine
#check @TheoremT.Continuum.epsilonPairKSPotential_energy_affine
#check @TheoremT.Continuum.epsilonPairKSPotential_eq_coulomb_scaled
#check @TheoremT.Continuum.epsilonPairKSPotential_on_zero
#check @TheoremT.Continuum.epsilonPairKSPotential_contDiffAt

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.epsilonNuclearKSPotential
#print axioms TheoremT.Continuum.nuclearKSPotential_energy_affine
#print axioms TheoremT.Continuum.epsilonNuclearKSPotential_energy_affine
#print axioms TheoremT.Continuum.epsilonNuclearKSPotential_eq_coulomb_scaled
#print axioms TheoremT.Continuum.epsilonNuclearKSPotential_on_zero
#print axioms TheoremT.Continuum.epsilonNuclearKSPotential_contDiffAt
#print axioms TheoremT.Continuum.epsilonPairKSPotential
#print axioms TheoremT.Continuum.pairKSPotential_energy_affine
#print axioms TheoremT.Continuum.epsilonPairKSPotential_energy_affine
#print axioms TheoremT.Continuum.epsilonPairKSPotential_eq_coulomb_scaled
#print axioms TheoremT.Continuum.epsilonPairKSPotential_on_zero
#print axioms TheoremT.Continuum.epsilonPairKSPotential_contDiffAt
