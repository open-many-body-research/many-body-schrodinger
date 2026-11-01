import KSCircleContinuousLinear_v1
import KSPhysicalCircleInvariance_v1

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
#check @TheoremT.Continuum.ksCircleActionCLM
#check @TheoremT.Continuum.ksCircleActionCLM_apply
#check @TheoremT.Continuum.ksCircleAction_norm
#check @TheoremT.Continuum.ksCircleActionCLM_norm
#check @TheoremT.Continuum.ksCircleProductCLM
#check @TheoremT.Continuum.ksCircleProductCLM_apply
#check @TheoremT.Continuum.ksCircleProductCLM_fixed
#check @TheoremT.Continuum.ksCircleProductCLM_norm
#check @TheoremT.Continuum.ksCircleProductCLM_pullback_invariant
#check @TheoremT.Continuum.nuclearKSLift_physical_circle_invariant
#check @TheoremT.Continuum.pairKSLift_physical_circle_invariant
#check @TheoremT.Continuum.nuclearKSPhysicalPullback_circle_invariant
#check @TheoremT.Continuum.pairKSPhysicalPullback_circle_invariant

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksCircleActionCLM
#print axioms TheoremT.Continuum.ksCircleActionCLM_apply
#print axioms TheoremT.Continuum.ksCircleAction_norm
#print axioms TheoremT.Continuum.ksCircleActionCLM_norm
#print axioms TheoremT.Continuum.ksCircleProductCLM
#print axioms TheoremT.Continuum.ksCircleProductCLM_apply
#print axioms TheoremT.Continuum.ksCircleProductCLM_fixed
#print axioms TheoremT.Continuum.ksCircleProductCLM_norm
#print axioms TheoremT.Continuum.ksCircleProductCLM_pullback_invariant
#print axioms TheoremT.Continuum.nuclearKSLift_physical_circle_invariant
#print axioms TheoremT.Continuum.pairKSLift_physical_circle_invariant
#print axioms TheoremT.Continuum.nuclearKSPhysicalPullback_circle_invariant
#print axioms TheoremT.Continuum.pairKSPhysicalPullback_circle_invariant
