import PhysicalSpectatorReindexAll_v1
import SecondDirectionalLinearAt_v1
import WeakGrushinCutoffNormCoefficients_v1

/-! Exact cutoff transport for either selected electron in N=2. All spectator
sums are transported through the proved selected-electron index equivalence. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem physicalSpectatorReindexAt_cutoff_test (i : Fin 2)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (χ ∘ physicalSpectatorReindexAt i) ∧
      HasCompactSupport (χ ∘ physicalSpectatorReindexAt i) ∧
      tsupport (χ ∘ physicalSpectatorReindexAt i) =
        physicalSpectatorReindexAt i ⁻¹' tsupport χ := by
  exact ⟨hχ.comp (physicalSpectatorReindexAt_contDiff i),
    hc.comp_homeomorph (physicalSpectatorHomeomorphAt i),
    tsupport_comp_eq_preimage χ (physicalSpectatorHomeomorphAt i)⟩

theorem physicalSpectatorReindexAt_cutoff_first (i : Fin 2)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (p v : Space (SpectatorCoordinate i)) :
    fderiv ℝ (χ ∘ physicalSpectatorReindexAt i) p v =
      fderiv ℝ χ (physicalSpectatorReindexAt i p) (physicalSpectatorReindexAt i v) := by
  have hχd : DifferentiableAt ℝ χ (physicalSpectatorReindexAt i p) :=
    (hχ.differentiable (by simp)).differentiableAt
  rw [fderiv_comp p hχd (physicalSpectatorReindexAt i).toContinuousLinearMap.differentiableAt,
    (physicalSpectatorReindexAt i).hasFDerivAt.fderiv]
  rfl

theorem physicalSpectatorReindexAt_cutoff_second (i : Fin 2)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (p v w : Space (SpectatorCoordinate i)) :
    fderiv ℝ (fun q => fderiv ℝ (χ ∘ physicalSpectatorReindexAt i) q v) p w =
      fderiv ℝ (fun q => fderiv ℝ χ q (physicalSpectatorReindexAt i v))
        (physicalSpectatorReindexAt i p) (physicalSpectatorReindexAt i w) :=
  second_directional_linear_at (physicalSpectatorReindexAt i).toContinuousLinearMap p v w
    (hχ.contDiffAt.of_le (by simp))

theorem physicalSpectatorReindexAt_combinedCutoffScalar (i : Fin 2) (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (p : Space (SpectatorCoordinate i)) :
    combinedCutoffScalar c (χ ∘ physicalSpectatorReindexAt i) p =
      combinedCutoffScalar c χ (physicalSpectatorReindexAt i p) := by
  simp only [combinedCutoffScalar,physicalSpectatorReindexAt_cutoff_second i hχ,
    physicalSpectatorReindexAt_yDir,physicalSpectatorReindexAt_tDir]
  rw [(twoElectronSpectatorCoordinateEquiv i).sum_comp (fun j : Fin 3 =>
    fderiv ℝ (fun q => fderiv ℝ χ q (tDir j))
      (physicalSpectatorReindexAt i p) (tDir j))]
  rfl

theorem physicalSpectatorReindexAt_cutoffGradientWeight (i : Fin 2) (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (p : Space (SpectatorCoordinate i)) :
    cutoffGradientWeight c (χ ∘ physicalSpectatorReindexAt i) p =
      cutoffGradientWeight c χ (physicalSpectatorReindexAt i p) := by
  simp only [cutoffGradientWeight,physicalSpectatorReindexAt_cutoff_first i hχ,
    physicalSpectatorReindexAt_yDir,physicalSpectatorReindexAt_tDir]
  rw [(twoElectronSpectatorCoordinateEquiv i).sum_comp (fun j : Fin 3 =>
    (fderiv ℝ χ (physicalSpectatorReindexAt i p) (tDir j))^2)]
  rfl

theorem physicalSpectatorReindexAt_grushinCutoffWeight (i : Fin 2) (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ) (p : Space (SpectatorCoordinate i)) :
    grushinCutoffWeight c (χ ∘ physicalSpectatorReindexAt i) p =
      grushinCutoffWeight c χ (physicalSpectatorReindexAt i p) := by
  rw [← cutoffGradientWeight_eq_grushinCutoffWeight,← cutoffGradientWeight_eq_grushinCutoffWeight]
  exact physicalSpectatorReindexAt_cutoffGradientWeight i c hχ p

#print axioms physicalSpectatorReindexAt_cutoff_test
#print axioms physicalSpectatorReindexAt_cutoff_first
#print axioms physicalSpectatorReindexAt_cutoff_second
#print axioms physicalSpectatorReindexAt_combinedCutoffScalar
#print axioms physicalSpectatorReindexAt_cutoffGradientWeight
#print axioms physicalSpectatorReindexAt_grushinCutoffWeight
end TheoremT.Continuum.WeakGrushin
