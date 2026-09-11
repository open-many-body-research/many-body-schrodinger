import CompactCutoffDirectionalJets_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_cutoff_directional_energy {η : E → ℝ} {u : E → F}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hu : ContDiff ℝ ∞ u) (v : E) :
    (∫ x, ‖fderiv ℝ (fun y => η y • u y) x v‖^2 ∂μ) =
      -(∫ x, inner ℝ ((η x)^2 • u x)
        (fderiv ℝ (fun y => fderiv ℝ u y v) x v) ∂μ) +
      (∫ x, ‖(fderiv ℝ η x v) • u x‖^2 ∂μ) := by
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ u x v) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hηd : ContDiff ℝ ∞ (fun x => fderiv ℝ η x v) :=
    (hη.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hca : HasCompactSupport (fun x => η x • fderiv ℝ u x v) := by
    apply hc.mono
    intro x hx
    change η x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hcb : HasCompactSupport (fun x => (fderiv ℝ η x v) • u x) := by
    apply (hc.fderiv_apply ℝ v).mono
    intro x hx
    change fderiv ℝ η x v ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hc2 : HasCompactSupport (fun x => (η x)^2 • u x) := by
    apply hc.mono
    intro x hx
    change η x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have ia : Integrable (fun x => ‖η x • fderiv ℝ u x v‖^2) μ := by
    simpa only [Pi.smul_def', real_inner_self_eq_norm_sq] using
      compact_real_inner_integrable_general (hη.smul hd).continuous (hη.smul hd).continuous hca
  have ib : Integrable (fun x => ‖(fderiv ℝ η x v) • u x‖^2) μ := by
    simpa only [Pi.smul_def', real_inner_self_eq_norm_sq] using
      compact_real_inner_integrable_general (hηd.smul hu).continuous (hηd.smul hu).continuous hcb
  have iab := compact_real_inner_integrable_general (μ := μ)
    (hηd.smul hu).continuous (hη.smul hd).continuous hcb
  simp only [Pi.smul_def'] at iab
  have ia2 : Integrable (fun x => ‖η x • fderiv ℝ u x v‖^2 +
      2*inner ℝ ((fderiv ℝ η x v) • u x) (η x • fderiv ℝ u x v)) μ :=
    ia.add (iab.const_mul 2)
  have hn : (∫ x, ‖fderiv ℝ (fun y => η y • u y) x v‖^2 ∂μ) =
      (∫ x, ‖η x • fderiv ℝ u x v‖^2 ∂μ) +
      2*(∫ x, inner ℝ ((fderiv ℝ η x v) • u x) (η x • fderiv ℝ u x v) ∂μ) +
      (∫ x, ‖(fderiv ℝ η x v) • u x‖^2 ∂μ) := by
    simp_rw [cutoff_directional_norm_square hη hu]
    rw [integral_add ia2 ib,
      integral_add ia (iab.const_mul 2), integral_const_mul]
  have hi := compact_directional_inner_ibp (μ := μ) ((hη.pow 2).smul hu) hd hc2 v
  simp only [Pi.smul_def'] at hi
  simp_rw [cutoff_square_directional_inner hη hu] at hi
  rw [integral_add ia (iab.const_mul 2), integral_const_mul] at hi
  linarith

#print axioms compact_cutoff_directional_energy
end TheoremT.Continuum
