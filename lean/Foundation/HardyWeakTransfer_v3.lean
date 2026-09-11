import HardyWeakTransfer_v2
import HardyLimitAsymptotic_v1

/-! The full smooth-core to actual weak-H¹ transfer, preserving the exact
constant. Cutoff and mollifier families are constructed in proved dependencies. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology
namespace TheoremT.Continuum

/-- Every nonnegative weighted gradient inequality on compact smooth functions
extends, with the same constant, to the already defined distributional weak H¹
domain. The smooth-core inequality is the sole analytic premise. -/
theorem compact_core_bound_extends_weakH1 {N : ℕ} (W : Configuration N → ℝ)
    (hW : ∀ x, 0 ≤ W x) {K : ℝ} (hK : 0 ≤ K)
    (hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => W x * ‖u x‖^2) volume ∧
        (∫ x, W x * ‖u x‖^2) ≤ K *
          (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2))
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => W x * ‖f x‖^2) volume ∧
      (∫ x, W x * ‖f x‖^2) ≤ K * (∑ k : Coordinate N, ‖d k‖^2) := by
  obtain ⟨C, hC0, hC⟩ := scaledCutoff_derivative_bound N
  let R : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hR : ∀ n, 0 < R n := by intro n; dsimp [R]; positivity
  let t : ℕ → ℝ := fun n => (R n)⁻¹
  have htpos : ∀ n, 0 < t n := fun n => inv_pos.mpr (hR n)
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa only [t, R, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  let G : ℝ := ∑ k : Coordinate N, ‖d k‖^2
  let M : ℝ := Fintype.card (Coordinate N)
  let fn : ℕ → SpatialL2 N := fun n =>
    cutoffMul (scaledCutoff N (R n)) (scaledCutoff_contDiff N (R n)).continuous
      (scaledCutoff_hasCompactSupport N (hR n)) f
  let B : ℕ → ℝ := fun n =>
    K * ((1+t n)*G + ((1+t n)*t n)*(M*C^2)*‖f‖^2)
  have hcut n := compact_core_bound_for_cutoff W hW hK hcore f d hd
    (scaledCutoff N (R n)) (scaledCutoff_contDiff N (R n))
    (scaledCutoff_hasCompactSupport N (hR n))
  have hbound : ∀ n, (∫ x, W x * ‖fn n x‖^2) ≤ B n := by
    intro n
    have hb := cutoff_gradient_square_bound
      (scaledCutoff N (R n)) (scaledCutoff_contDiff N (R n))
      (scaledCutoff_hasCompactSupport N (hR n)) f d (fun _ => C / R n)
      (scaledCutoff_norm_le_one N (R n))
      (fun _ => div_nonneg hC0 (hR n).le)
      (fun k x => hC (R n) (hR n) x k) (htpos n)
    have hh := (hcut n).2.trans (mul_le_mul_of_nonneg_left hb hK)
    change (∫ x, W x * ‖fn n x‖^2) ≤ _ at hh
    convert hh using 1
    dsimp [B, t, G, M]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_inv]
    field_simp [(hR n).ne']
    ring
  have hBt : Tendsto B atTop (𝓝 (K*G)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hv := ((hone.add ht).mul_const G).add
      ((((hone.add ht).mul ht).mul_const (M*C^2)).mul_const (‖f‖^2))
    simpa [B] using hv.const_mul K
  have hae : ∀ᵐ x : Configuration N, ∀ n,
      fn n x = scaledCutoff N (R n) x • f x := by
    rw [ae_all_iff]
    intro n
    exact cutoffMul_ae _ _ _ f
  have hflim : ∀ᵐ x : Configuration N,
      Tendsto (fun n => W x * ‖fn n x‖^2) atTop (𝓝 (W x * ‖f x‖^2)) := by
    filter_upwards [hae] with x hx
    have hv : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
      simp_rw [hx]
      have hh := ((scaledCutoff_tendsto_one N x).comp hRt).smul
        (tendsto_const_nhds (x := f x))
      simpa using hh
    exact tendsto_const_nhds.mul (hv.norm.pow 2)
  exact TheoremT.HardyLimit.integrable_and_integral_le_of_nonneg_limit_varying_bounds
    (fun n => (hcut n).1)
    (fun _ => Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _)))
    (Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _)))
    hflim hbound hBt

#print axioms compact_core_bound_extends_weakH1
end TheoremT.Continuum
