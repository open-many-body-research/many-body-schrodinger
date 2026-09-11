import ActualWeakOrder_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv
namespace TheoremT.Continuum

theorem hasWeakOrder_add_two_of_laplacian {N : ℕ} {n : ℕ} {f g : SpatialL2 N}
    (hΔ : Δ (f : 𝓢'(Configuration N,ℂ)) = (g : 𝓢'(Configuration N,ℂ)))
    (hg : HasWeakOrder g n) : HasWeakOrder f (n+2) := by
  induction n generalizing f g with
  | zero =>
    exact (hasWeakOrder_two_iff f).mpr (hasH2_of_temperedDistribution_laplacian f g hΔ)
  | succ n ih =>
    obtain ⟨e,he,hee⟩ := hg
    obtain ⟨d,hd,_⟩ := hasH2_of_temperedDistribution_laplacian f g hΔ
    change ∃ d' : Coordinate N → SpatialL2 N,
      (∀ k, WeakPartial f (d' k) k) ∧ ∀ k, HasWeakOrder (d' k) (n+2)
    refine ⟨d,hd,fun k => ?_⟩
    apply ih (g := e k) _ (hee k)
    rw [← (hd k).temperedDistribution_derivative,distribution_laplacian_derivative_commute,
      hΔ,(he k).temperedDistribution_derivative]

#print axioms hasWeakOrder_add_two_of_laplacian
end TheoremT.Continuum
