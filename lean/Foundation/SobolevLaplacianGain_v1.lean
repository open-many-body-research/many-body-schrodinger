import LaplacianSobolevBridge_v1

noncomputable section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian ENNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memSobolev_add_two_of_laplacian {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev s p u) (hΔ : MemSobolev s p (Δ u)) :
    MemSobolev (s+2) p u := by
  have hh : MemSobolev s p (besselPotential E ℂ 2 u) := by
    rw [besselPotential_two_eq_sub_laplacian]
    have hs := hΔ.smul ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ)
    simpa only [Complex.coe_smul] using hu.sub hs
  simpa only [add_comm] using memSobolev_besselPotential_iff.mp hh

#print axioms memSobolev_add_two_of_laplacian
end TheoremT.Continuum
