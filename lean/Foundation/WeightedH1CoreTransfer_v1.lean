import HardyH1ScalarDensity_v2
import HardyWeakTransfer_v2
import HardyLimitAsymptotic_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A reusable actual weak-H¹ transfer with any finite selection of coordinate
energies and a mass term. The smooth approximation sequence is fully proved. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace TheoremT.Continuum

theorem spatialL2_partial_family_integral_eq {N : ℕ}
    (S : Finset (Coordinate N)) (d : Coordinate N → SpatialL2 N) :
    (∫ x, ∑ k ∈ S, ‖d k x‖^2) = ∑ k ∈ S, ‖d k‖^2 := by
  rw [integral_finsetSum S
    (fun k _ => (Lp.memLp (d k)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
  simp_rw [← spatialL2_norm_sq_eq_integral]

/-- Every nonnegative weighted quadratic estimate on the compact smooth core,
with a mass term and selected directional energies, holds on actual weak H¹.
The explicit core premise is intended for separate proved physical instantiations. -/
theorem weighted_compact_core_bound_extends_weakH1 {N : ℕ}
    (S : Finset (Coordinate N)) (W : Configuration N → ℝ)
    (hW : ∀ x, 0 ≤ W x) (A K : ℝ)
    (hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => W x * ‖u x‖^2) volume ∧
        (∫ x, W x * ‖u x‖^2) ≤ A * (∫ x, ‖u x‖^2) + K *
          (∫ x, ∑ k ∈ S, ‖smoothPartial u k x‖^2))
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => W x * ‖f x‖^2) volume ∧
      (∫ x, W x * ‖f x‖^2) ≤ A * ‖f‖^2 + K * (∑ k ∈ S, ‖d k‖^2) := by
  classical
  obtain ⟨u,g,dg,hu,huc,hgu,hdgu,_hdg,_hH2,hgf,hdgd⟩ :=
    weakH1_smooth_compact_graph_sequence d hd
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hgf).exists_seq_tendsto_ae
  have hcore' (n : ℕ) : Integrable (fun x => W x * ‖g n x‖^2) volume ∧
      (∫ x, W x * ‖g n x‖^2) ≤ A * ‖g n‖^2 + K * (∑ k ∈ S, ‖dg n k‖^2) := by
    have hc := hcore (u n) (hu n) (huc n)
    have hw : (fun x => W x * ‖g n x‖^2) =ᵐ[volume]
        (fun x => W x * ‖u n x‖^2) := by
      filter_upwards [hgu n] with x hx
      rw [hx]
    have hm : (∫ x, ‖u n x‖^2) = ‖g n‖^2 := by
      rw [spatialL2_norm_sq_eq_integral]
      exact integral_congr_ae ((hgu n).fun_comp (fun z => ‖z‖^2)).symm
    have he : (∫ x, ∑ k ∈ S, ‖smoothPartial (u n) k x‖^2) =
        ∑ k ∈ S, ‖dg n k‖^2 := by
      rw [← spatialL2_partial_family_integral_eq S]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 (hdgu n)] with x hx
      exact Finset.sum_congr rfl (fun k _ => congrArg (fun z : ℂ => ‖z‖^2) (hx k).symm)
    refine ⟨hc.1.congr hw.symm, ?_⟩
    rw [integral_congr_ae hw, ← hm, ← he]
    exact hc.2
  apply TheoremT.HardyLimit.integrable_and_integral_le_of_nonneg_limit_varying_bounds
    (fun n => (hcore' (φ n)).1)
    (fun n => Filter.Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _)))
    (Filter.Eventually.of_forall (fun x => mul_nonneg (hW x) (sq_nonneg _)))
  · filter_upwards [hφae] with x hx
    exact tendsto_const_nhds.mul (hx.norm.pow 2)
  · exact fun n => (hcore' (φ n)).2
  · apply Filter.Tendsto.add
    · exact tendsto_const_nhds.mul ((hgf.comp hφ.tendsto_atTop).norm.pow 2)
    · apply tendsto_const_nhds.mul
      exact tendsto_finset_sum S (fun k _ => ((hdgd k).comp hφ.tendsto_atTop).norm.pow 2)

#print axioms weighted_compact_core_bound_extends_weakH1
end TheoremT.Continuum
