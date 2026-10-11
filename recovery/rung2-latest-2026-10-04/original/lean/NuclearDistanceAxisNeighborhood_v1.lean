import NuclearDistanceAxisMap_v1

/-! An explicit nuclear distance polydisc and its image inside the half
polyradii for the axis-descended series. All coordinates remain complex. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def nuclearDistancePolydisc (σ δ : ℝ) : Set (Fin 3 → ℂ) :=
  {q | ‖q 0‖ < δ ∧ ‖q 1 - (σ : ℂ)‖ < δ ∧ ‖q 2 - (σ : ℂ)‖ < δ}

theorem nuclearDistanceAxis_denominator_ne_zero {σ δ : ℝ} (hσ : 0 < σ)
    (hδσ : δ ≤ σ / 4) {q : Fin 3 → ℂ} (hq : q ∈ nuclearDistancePolydisc σ δ) :
    2 * q 1 ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (nuclearDistanceAxis_bounds hσ hδσ q hq.1 hq.2.1 hq.2.2).1

theorem nuclearDistanceAxisMap_analyticOnNhd_polydisc {σ δ : ℝ} (hσ : 0 < σ)
    (hδσ : δ ≤ σ / 4) :
    AnalyticOnNhd ℂ nuclearDistanceAxisMap (nuclearDistancePolydisc σ δ) := by
  intro q hq
  exact nuclearDistanceAxisMap_analyticOnNhd q
    (nuclearDistanceAxis_bounds hσ hδσ q hq.1 hq.2.1 hq.2.2).1

theorem nuclearDistanceAxis_half_polyradii {σ δ h : ℝ} (hσ : 0 < σ)
    (hh : 0 < h) (hδσ : δ ≤ σ / 4) (hδh : δ ≤ h / 16)
    {q : Fin 3 → ℂ} (hq : q ∈ nuclearDistancePolydisc σ δ) :
    ‖nuclearDistanceAxisZ q‖ ≤ h / 4 ∧
      ‖nuclearDistanceAxisW q‖ < h^2 / 2 ∧
      ‖q 1 - (σ : ℂ)‖ < h / 16 := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hq.1.le
  obtain ⟨_, hz, hw⟩ := nuclearDistanceAxis_bounds hσ hδσ q hq.1 hq.2.1 hq.2.2
  refine ⟨hz.trans (by linarith), ?_, hq.2.1.trans_le hδh⟩
  have hsq : δ^2 ≤ (h / 16)^2 :=
    (sq_le_sq₀ hδ (by positivity)).mpr hδh
  nlinarith [sq_pos_of_pos hh]

end TheoremT.Continuum
