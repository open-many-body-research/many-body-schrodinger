import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Literal nuclear distance-to-axis coordinates. The three complex inputs
are ordered (r,s,u). Only s is divided by; no square root or area occurs.
The quantitative theorem holds on a closed polydisc and does not need the
additional restriction delta <= 1 from the paper. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def nuclearDistanceAxisZ (q : Fin 3 → ℂ) : ℂ :=
  ((q 0)^2 + (q 1)^2 - (q 2)^2) / (2 * q 1)

def nuclearDistanceAxisW (q : Fin 3 → ℂ) : ℂ :=
  (q 0)^2 - (nuclearDistanceAxisZ q)^2

def nuclearDistanceAxisMap (q : Fin 3 → ℂ) : Fin 2 → ℂ :=
  ![nuclearDistanceAxisZ q, nuclearDistanceAxisW q]

theorem nuclearDistanceAxisZ_analyticAt (q : Fin 3 → ℂ) (hs : q 1 ≠ 0) :
    AnalyticAt ℂ nuclearDistanceAxisZ q := by
  have hi (i : Fin 3) : AnalyticAt ℂ (fun p : Fin 3 → ℂ => p i) q :=
    (ContinuousLinearMap.proj i : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q
  exact (((hi 0).pow 2).add ((hi 1).pow 2) |>.sub ((hi 2).pow 2)).div
    ((analyticAt_const).mul (hi 1)) (mul_ne_zero (by norm_num) hs)

theorem nuclearDistanceAxisW_analyticAt (q : Fin 3 → ℂ) (hs : q 1 ≠ 0) :
    AnalyticAt ℂ nuclearDistanceAxisW q := by
  exact ((ContinuousLinearMap.proj 0 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt q).pow 2
    |>.sub ((nuclearDistanceAxisZ_analyticAt q hs).pow 2)

theorem nuclearDistanceAxisMap_analyticOnNhd :
    AnalyticOnNhd ℂ nuclearDistanceAxisMap {q | q 1 ≠ 0} := by
  intro q hq
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact nuclearDistanceAxisZ_analyticAt q hq
  · exact nuclearDistanceAxisW_analyticAt q hq

theorem nuclearDistanceAxisMap_center (σ : ℝ) :
    nuclearDistanceAxisMap ![0, (σ : ℂ), (σ : ℂ)] = 0 := by
  ext i
  fin_cases i <;> simp [nuclearDistanceAxisMap, nuclearDistanceAxisZ,
    nuclearDistanceAxisW]

theorem nuclearDistanceAxis_bounds_closed {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 ≤ δ) (hδσ : δ ≤ σ / 4) (q : Fin 3 → ℂ)
    (hr : ‖q 0‖ ≤ δ) (hs : ‖q 1 - (σ : ℂ)‖ ≤ δ)
    (hu : ‖q 2 - (σ : ℂ)‖ ≤ δ) :
    q 1 ≠ 0 ∧ ‖nuclearDistanceAxisZ q‖ ≤ 4 * δ ∧
      ‖nuclearDistanceAxisW q‖ ≤ 17 * δ^2 := by
  have hσnorm : ‖(σ : ℂ)‖ = σ := by simp [Complex.norm_real, abs_of_pos hσ]
  have hslow : σ - δ ≤ ‖q 1‖ := by
    have h := norm_sub_norm_le (σ : ℂ) (q 1)
    rw [hσnorm, norm_sub_rev] at h
    linarith
  have hspos : 0 < ‖q 1‖ := by linarith
  have hsne : q 1 ≠ 0 := norm_pos_iff.mp hspos
  have hsdiff : ‖q 1 - q 2‖ ≤ 2 * δ := by
    calc
      ‖q 1 - q 2‖ = ‖(q 1 - (σ : ℂ)) - (q 2 - (σ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖q 1 - (σ : ℂ)‖ + ‖q 2 - (σ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * δ := by linarith
  have hsupper : ‖q 1‖ ≤ σ + δ := by
    calc
      ‖q 1‖ = ‖(q 1 - (σ : ℂ)) + (σ : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖q 1 - (σ : ℂ)‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
      _ ≤ σ + δ := by rw [hσnorm]; linarith
  have huupper : ‖q 2‖ ≤ σ + δ := by
    calc
      ‖q 2‖ = ‖(q 2 - (σ : ℂ)) + (σ : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖q 2 - (σ : ℂ)‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
      _ ≤ σ + δ := by rw [hσnorm]; linarith
  have hssum : ‖q 1 + q 2‖ ≤ 2 * σ + 2 * δ := by
    exact (norm_add_le _ _).trans (by linarith)
  have hrpow : ‖q 0‖^2 ≤ δ^2 := (sq_le_sq₀ (norm_nonneg _) hδ).mpr hr
  have hnumerator : ‖(q 0)^2 + (q 1)^2 - (q 2)^2‖ ≤
      δ^2 + (2 * δ) * (2 * σ + 2 * δ) := by
    calc
      ‖(q 0)^2 + (q 1)^2 - (q 2)^2‖ =
          ‖(q 0)^2 + (q 1 - q 2) * (q 1 + q 2)‖ := by congr 1; ring
      _ ≤ ‖(q 0)^2‖ + ‖(q 1 - q 2) * (q 1 + q 2)‖ := norm_add_le _ _
      _ = ‖q 0‖^2 + ‖q 1 - q 2‖ * ‖q 1 + q 2‖ := by rw [norm_pow, norm_mul]
      _ ≤ δ^2 + (2 * δ) * (2 * σ + 2 * δ) :=
        add_le_add hrpow (mul_le_mul hsdiff hssum (norm_nonneg _) (by positivity))
  have hsmall : δ^2 ≤ σ / 4 * δ := by nlinarith [mul_le_mul_of_nonneg_right hδσ hδ]
  have hz : ‖nuclearDistanceAxisZ q‖ ≤ 4 * δ := by
    rw [nuclearDistanceAxisZ, norm_div, norm_mul]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ‖q 1‖)).mpr
    have hmul := mul_le_mul_of_nonneg_right hslow hδ
    nlinarith
  refine ⟨hsne, hz, ?_⟩
  calc
    ‖nuclearDistanceAxisW q‖ ≤ ‖(q 0)^2‖ + ‖(nuclearDistanceAxisZ q)^2‖ := norm_sub_le _ _
    _ = ‖q 0‖^2 + ‖nuclearDistanceAxisZ q‖^2 := by rw [norm_pow, norm_pow]
    _ ≤ δ^2 + (4 * δ)^2 :=
      add_le_add hrpow ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz)
    _ = 17 * δ^2 := by ring

theorem nuclearDistanceAxis_bounds {σ δ : ℝ} (hσ : 0 < σ)
    (hδσ : δ ≤ σ / 4) (q : Fin 3 → ℂ)
    (hr : ‖q 0‖ < δ) (hs : ‖q 1 - (σ : ℂ)‖ < δ)
    (hu : ‖q 2 - (σ : ℂ)‖ < δ) :
    q 1 ≠ 0 ∧ ‖nuclearDistanceAxisZ q‖ ≤ 4 * δ ∧
      ‖nuclearDistanceAxisW q‖ ≤ 17 * δ^2 := by
  exact nuclearDistanceAxis_bounds_closed hσ ((norm_nonneg _).trans hr.le) hδσ q
    hr.le hs.le hu.le

end TheoremT.Continuum
