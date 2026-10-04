import LocalProductDirectionalWeakLinear_v1

-- Human-readable physical definitions.

-- Expanded types expose mathematical implicit arguments; declaration bodies stay in source.
-- Instance implementations are suppressed; proof arguments in types are printed.
set_option pp.all true
set_option pp.universes true
set_option pp.instances false
set_option pp.proofs true
set_option pp.maxSteps 2000000
#check @TheoremT.Continuum.ProductLocalWeakDirectional.zero
#check @TheoremT.Continuum.ProductLocalWeakDirectional.add
#check @TheoremT.Continuum.ProductLocalWeakDirectional.neg
#check @TheoremT.Continuum.ProductLocalWeakDirectional.sub
#check @TheoremT.Continuum.ProductLocalWeakDirectional.const_smul
#check @TheoremT.Continuum.ProductLocalWeakDirectional.finset_sum
#check @TheoremT.Continuum.ProductLocalWeakDirectional.congr_ae_local

set_option pp.all false
set_option pp.universes false
-- Kernel axiom dependencies for every local declaration.
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.zero
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.add
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.neg
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.sub
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.const_smul
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.finset_sum
#print axioms TheoremT.Continuum.ProductLocalWeakDirectional.congr_ae_local
