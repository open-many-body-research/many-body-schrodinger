import SpectatorScalingContinuousLinearMap_v1
import IteratedFDerivLinearCompositionAt_v1
import SpectatorScalingIteratedDerivativeWord_v1

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
#check @TheoremT.Continuum.spectatorScalingCoefficient
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap_coe
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap_single
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single_inl
#check @TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single_inr
#check @TheoremT.Continuum.iteratedFDeriv_comp_right_of_contDiffAt
#check @TheoremT.Continuum.spectatorScaling_iteratedFDeriv_word
#check @TheoremT.Continuum.spectatorScaling_iteratedFDeriv_word_norm_le

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.spectatorScalingCoefficient
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap_coe
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap_single
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single_inl
#print axioms TheoremT.Continuum.spectatorScalingContinuousLinearMap_norm_single_inr
#print axioms TheoremT.Continuum.iteratedFDeriv_comp_right_of_contDiffAt
#print axioms TheoremT.Continuum.spectatorScaling_iteratedFDeriv_word
#print axioms TheoremT.Continuum.spectatorScaling_iteratedFDeriv_word_norm_le
