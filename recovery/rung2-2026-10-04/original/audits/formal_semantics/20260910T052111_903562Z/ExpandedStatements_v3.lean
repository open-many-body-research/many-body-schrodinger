import TwoElectronEigenSinglet_v1
import TwoElectronGroundSpatial_v1
import TwoElectronUniformGap_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.spinSingletLift_hydrogen_inner
#check @TheoremT.Continuum.twoElectron_low_eigen_zero_of_overlap_zero
#check @TheoremT.Continuum.twoElectron_low_eigen_singlet
#check @TheoremT.Continuum.twoElectron_low_eigen_spatial_amplitude
#check @TheoremT.Continuum.twoElectron_ground_spatial_eigenfunction
#check @TheoremT.Continuum.hydrogenProductRepulsion_le_five_sevenths
#check @TheoremT.Continuum.twoElectron_ground_energy_upper
#check @TheoremT.Continuum.twoElectron_ground_energy_uniform_upper
#check @TheoremT.Continuum.twoElectron_ground_separator_gap
#check @TheoremT.Continuum.twoElectron_ground_uniform_spectral_gap
#check @TheoremT.Continuum.helium_ground_uniform_spectral_gap

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spinSingletLift_hydrogen_inner
#print axioms TheoremT.Continuum.twoElectron_low_eigen_zero_of_overlap_zero
#print axioms TheoremT.Continuum.twoElectron_low_eigen_singlet
#print axioms TheoremT.Continuum.twoElectron_low_eigen_spatial_amplitude
#print axioms TheoremT.Continuum.twoElectron_ground_spatial_eigenfunction
#print axioms TheoremT.Continuum.hydrogenProductRepulsion_le_five_sevenths
#print axioms TheoremT.Continuum.twoElectron_ground_energy_upper
#print axioms TheoremT.Continuum.twoElectron_ground_energy_uniform_upper
#print axioms TheoremT.Continuum.twoElectron_ground_separator_gap
#print axioms TheoremT.Continuum.twoElectron_ground_uniform_spectral_gap
#print axioms TheoremT.Continuum.helium_ground_uniform_spectral_gap
