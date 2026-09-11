import ActualH2DomainEquivalence_v1

set_option pp.maxSteps 1000000
set_option pp.all true
#check @TheoremT.Continuum.HasH2.exists_temperedDistribution_laplacian
#check @TheoremT.Continuum.hasH2_iff_exists_temperedDistribution_laplacian
#check @TheoremT.Continuum.hasH2_iff_memSobolev_two
#check @TheoremT.Continuum.hasH2_iff_fourier_normSq_memLp
set_option pp.all false
#print TheoremT.Continuum.HasH2
#print TheoremT.Continuum.WeakPartial
#print axioms TheoremT.Continuum.HasH2.exists_temperedDistribution_laplacian
#print axioms TheoremT.Continuum.hasH2_iff_exists_temperedDistribution_laplacian
#print axioms TheoremT.Continuum.hasH2_iff_memSobolev_two
#print axioms TheoremT.Continuum.hasH2_iff_fourier_normSq_memLp
