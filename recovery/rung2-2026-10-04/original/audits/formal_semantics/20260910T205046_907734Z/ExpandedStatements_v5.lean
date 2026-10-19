import KSScaledAffineWeakForcing_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ksScaledPrincipal_const
#check @TheoremT.Continuum.ks_scaled_constant_weak_pairing
#check @TheoremT.Continuum.ks_scaled_affine_weak_forcing

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ksScaledPrincipal_const
#print axioms TheoremT.Continuum.ks_scaled_constant_weak_pairing
#print axioms TheoremT.Continuum.ks_scaled_affine_weak_forcing
