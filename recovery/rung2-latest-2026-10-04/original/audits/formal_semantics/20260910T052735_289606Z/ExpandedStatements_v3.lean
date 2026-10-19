import CoulombConjugation_v1
import TwoElectronGroundReal_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.spatialConj
#check @TheoremT.Continuum.spatialConj_coeFn
#check @TheoremT.Continuum.spatialConj_smul
#check @TheoremT.Continuum.spatialConj_involutive
#check @TheoremT.Continuum.spatialConj_pullback
#check @TheoremT.Continuum.spatialConj_integral_test
#check @TheoremT.Continuum.weakPartial_conj
#check @TheoremT.Continuum.scalar_graph_conj
#check @TheoremT.Continuum.spatialConj_fixed_im_zero
#check @TheoremT.Continuum.symmetric_eigen_has_real_nonzero
#check @TheoremT.Continuum.symmetric_eigen_has_real_unit
#check @TheoremT.Continuum.twoElectron_ground_real_spatial_eigenfunction

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spatialConj
#print axioms TheoremT.Continuum.spatialConj_coeFn
#print axioms TheoremT.Continuum.spatialConj_smul
#print axioms TheoremT.Continuum.spatialConj_involutive
#print axioms TheoremT.Continuum.spatialConj_pullback
#print axioms TheoremT.Continuum.spatialConj_integral_test
#print axioms TheoremT.Continuum.weakPartial_conj
#print axioms TheoremT.Continuum.scalar_graph_conj
#print axioms TheoremT.Continuum.spatialConj_fixed_im_zero
#print axioms TheoremT.Continuum.symmetric_eigen_has_real_nonzero
#print axioms TheoremT.Continuum.symmetric_eigen_has_real_unit
#print axioms TheoremT.Continuum.twoElectron_ground_real_spatial_eigenfunction
