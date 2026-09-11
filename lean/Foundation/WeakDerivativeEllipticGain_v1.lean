import DistributionDerivativeCommute_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv
namespace TheoremT.Continuum

theorem weakPartial_hasH2_of_laplacian_weakPartial {N : ℕ}
    {f d g e : SpatialL2 N} {k : Coordinate N}
    (hd : WeakPartial f d k)
    (hΔ : Δ (f : 𝓢'(Configuration N,ℂ)) = (g : 𝓢'(Configuration N,ℂ)))
    (he : WeakPartial g e k) : HasH2 d := by
  apply hasH2_of_temperedDistribution_laplacian d e
  rw [← hd.temperedDistribution_derivative,distribution_laplacian_derivative_commute,
    hΔ,he.temperedDistribution_derivative]

theorem exists_H2_first_jet_of_laplacian_H1 {N : ℕ} {f g : SpatialL2 N}
    (hΔ : Δ (f : 𝓢'(Configuration N,ℂ)) = (g : 𝓢'(Configuration N,ℂ)))
    (hg : HasH1 g) :
    ∃ d : Coordinate N → SpatialL2 N, (∀ k, WeakPartial f (d k) k) ∧
      ∀ k, HasH2 (d k) := by
  obtain ⟨d,hd,_⟩ := hasH2_of_temperedDistribution_laplacian f g hΔ
  obtain ⟨e,he⟩ := hg
  exact ⟨d,hd,fun k => weakPartial_hasH2_of_laplacian_weakPartial (hd k) hΔ (he k)⟩

#print axioms weakPartial_hasH2_of_laplacian_weakPartial
#print axioms exists_H2_first_jet_of_laplacian_H1
end TheoremT.Continuum
