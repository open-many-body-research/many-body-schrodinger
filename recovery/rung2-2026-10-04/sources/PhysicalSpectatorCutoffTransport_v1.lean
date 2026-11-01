import PhysicalSpectatorReindex_v1
import SecondDirectionalLinearAt_v1
import WeakGrushinCutoffNormCoefficients_v1

/-! Exact cutoff transport between the physical two-electron spectator index
and the three scheduled coordinates. Direction sums are reindexed by an actual
equivalence; all cutoff coefficients and numerical constants are preserved. -/
noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem physicalSpectatorReindex_cutoff_test {χ : Space (Fin 3) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (χ ∘ physicalSpectatorReindex) ∧
      HasCompactSupport (χ ∘ physicalSpectatorReindex) ∧
      tsupport (χ ∘ physicalSpectatorReindex) =
        physicalSpectatorReindex ⁻¹' tsupport χ := by
  exact ⟨hχ.comp physicalSpectatorReindex_contDiff,
    hc.comp_homeomorph physicalSpectatorHomeomorph,
    tsupport_comp_eq_preimage χ physicalSpectatorHomeomorph⟩

theorem physicalSpectatorReindex_cutoff_first {χ : Space (Fin 3) → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (p v : Space (SpectatorCoordinate (0 : Fin 2))) :
    fderiv ℝ (χ ∘ physicalSpectatorReindex) p v =
      fderiv ℝ χ (physicalSpectatorReindex p) (physicalSpectatorReindex v) := by
  have hχd : DifferentiableAt ℝ χ (physicalSpectatorReindex p) :=
    (hχ.differentiable (by simp)).differentiableAt
  rw [fderiv_comp p hχd physicalSpectatorReindex.toContinuousLinearMap.differentiableAt]
  rw [physicalSpectatorReindex.hasFDerivAt.fderiv]
  rfl

theorem physicalSpectatorReindex_cutoff_second {χ : Space (Fin 3) → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (p v w : Space (SpectatorCoordinate (0 : Fin 2))) :
    fderiv ℝ (fun q => fderiv ℝ (χ ∘ physicalSpectatorReindex) q v) p w =
      fderiv ℝ (fun q => fderiv ℝ χ q (physicalSpectatorReindex v))
        (physicalSpectatorReindex p) (physicalSpectatorReindex w) :=
  second_directional_linear_at physicalSpectatorReindex.toContinuousLinearMap p v w
    (hχ.contDiffAt.of_le (by simp))

theorem physicalSpectatorReindex_combinedCutoffScalar (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (p : Space (SpectatorCoordinate (0 : Fin 2))) :
    combinedCutoffScalar c (χ ∘ physicalSpectatorReindex) p =
      combinedCutoffScalar c χ (physicalSpectatorReindex p) := by
  simp only [combinedCutoffScalar,physicalSpectatorReindex_cutoff_second hχ,
    physicalSpectatorReindex_yDir,physicalSpectatorReindex_tDir]
  rw [physicalSpectatorReindex_apply p]
  congr 1

theorem physicalSpectatorReindex_cutoffGradientWeight (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (p : Space (SpectatorCoordinate (0 : Fin 2))) :
    cutoffGradientWeight c (χ ∘ physicalSpectatorReindex) p =
      cutoffGradientWeight c χ (physicalSpectatorReindex p) := by
  simp only [cutoffGradientWeight,physicalSpectatorReindex_cutoff_first hχ,
    physicalSpectatorReindex_yDir,physicalSpectatorReindex_tDir]
  rw [physicalSpectatorReindex_apply p]
  congr 1

theorem physicalSpectatorReindex_grushinCutoffWeight (c : ℝ)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (p : Space (SpectatorCoordinate (0 : Fin 2))) :
    grushinCutoffWeight c (χ ∘ physicalSpectatorReindex) p =
      grushinCutoffWeight c χ (physicalSpectatorReindex p) := by
  rw [← cutoffGradientWeight_eq_grushinCutoffWeight,
    ← cutoffGradientWeight_eq_grushinCutoffWeight]
  exact physicalSpectatorReindex_cutoffGradientWeight c hχ p

#print axioms physicalSpectatorReindex_cutoff_test
#print axioms physicalSpectatorReindex_cutoff_first
#print axioms physicalSpectatorReindex_cutoff_second
#print axioms physicalSpectatorReindex_combinedCutoffScalar
#print axioms physicalSpectatorReindex_cutoffGradientWeight
#print axioms physicalSpectatorReindex_grushinCutoffWeight
end TheoremT.Continuum.WeakGrushin
