import GrushinFactorialCutoffData_v1
import MeasureBoundedRealMultiplier_v1

/-! The weight-removal step consumed by the factorial localization
commutator. A multiplier supported away from Y=0 is controlled by the
four actual coordinate-square weighted L2 components. No unweighted
L2 hypothesis is placed on the function being localized. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoff_weight_removal_pointwise {k K a : ℝ} (hk : 0 < k) (hK : 0 ≤ K)
    (ha : |a| ≤ K) (y : EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (haway : a ≠ 0 → k ≤ ‖y‖) :
    ‖a • z‖ ≤ (K/k^2)*‖(‖y‖^2 : ℝ) • z‖ := by
  by_cases hz : a = 0
  · simp only [hz,zero_smul,norm_zero]
    positivity
  have hy := haway hz
  have hsq := pow_le_pow_left₀ hk.le hy 2
  have hratio : K ≤ (K/k^2)*‖y‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ K/k^2)
    have he : (K/k^2)*k^2 = K := by field_simp
    rwa [he] at hh
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y‖)]
  calc
    |a| * ‖z‖ ≤ K*‖z‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg z)
    _ ≤ ((K/k^2)*‖y‖^2)*‖z‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg z)
    _ = _ := by ring

theorem cutoff_weight_removal_L2 {μ : Measure (Space κ)} {f : Space κ → ℂ}
    (hf : AEStronglyMeasurable f μ) {a : Space κ → ℝ}
    (ha : AEStronglyMeasurable a μ) {k K : ℝ} (hk : 0 < k) (hK : 0 ≤ K)
    (hbound : ∀ᵐ p ∂μ, |a p| ≤ K)
    (haway : ∀ᵐ p ∂μ, a p ≠ 0 → k ≤ ‖p.1‖)
    (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ i, w i =ᵐ[μ] (fun p => (p.1 i)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ, u =ᵐ[μ] (fun p => a p • f p) ∧
      ‖u‖ ≤ (K/k^2)*(∑ i, ‖w i‖) := by
  let W : Lp ℂ 2 μ := ∑ i, w i
  have hW : W =ᵐ[μ] (fun p => (‖p.1‖^2 : ℝ) • f p) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ w,ae_all_iff.mpr hw] with p hp hwp
    change W p = _
    change (∑ i, w i) p = ∑ i, w i p at hp
    rw [hp]
    simp_rw [hwp]
    rw [← Finset.sum_smul,← EuclideanSpace.real_norm_sq_eq]
  have hb : ∀ᵐ p ∂μ, ‖a p • f p‖ ≤ (K/k^2)*‖W p‖ := by
    filter_upwards [hW,hbound,haway] with p hWp hbp hap
    rw [hWp]
    exact cutoff_weight_removal_pointwise hk hK hbp p.1 (f p) hap
  have hm : MemLp (fun p => a p • f p) 2 μ :=
    (Lp.memLp W).of_le_mul (ha.smul hf) hb
  let u : Lp ℂ 2 μ := hm.toLp (fun p => a p • f p)
  have hu : u =ᵐ[μ] (fun p => a p • f p) := MemLp.coeFn_toLp hm
  refine ⟨u,hu,?_⟩
  calc
    ‖u‖ ≤ (K/k^2)*‖W‖ := Lp.norm_le_mul_norm_of_ae_le_mul (by
      filter_upwards [hu,hb] with p hup hbp
      rwa [hup])
    _ ≤ (K/k^2)*(∑ i, ‖w i‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end TheoremT.Continuum.WeakGrushin
