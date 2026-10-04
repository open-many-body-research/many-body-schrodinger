import KSScaledPrincipal_v1
import KSScaledPrincipalIBP_v1
import KSScaledLocalWeakKernel_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksScaledPrincipal
#check @TheoremT.Continuum.ksScaledRealPrincipal
#check @TheoremT.Continuum.ksScaledPrincipal_four
#check @TheoremT.Continuum.ksScaledRealPrincipal_four
#check @TheoremT.Continuum.ks_scaled_principal_integration_by_parts
#check @TheoremT.Continuum.ks_scaled_local_classical_kernel_weak

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksScaledPrincipal
#print axioms TheoremT.Continuum.ksScaledRealPrincipal
#print axioms TheoremT.Continuum.ksScaledPrincipal_four
#print axioms TheoremT.Continuum.ksScaledRealPrincipal_four
#print axioms TheoremT.Continuum.ks_scaled_principal_integration_by_parts
#print axioms TheoremT.Continuum.ks_scaled_local_classical_kernel_weak
