import GrushinFactorialWeightedCutoffL2_v1

/-! The spectator portion of the factorial commutator already carries
the radial square. Its four coordinate-square components combine into
an actual L2 element before bounded multiplication. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem weightedCoordinateSum_ae {μ : Measure (Space κ)} {f : Space κ → ℂ}
    (w : Fin 4 → Lp ℂ 2 μ) (hw : ∀ i, w i =ᵐ[μ] (fun p => (p.1 i)^2 • f p)) :
    (∑ i, w i) =ᵐ[μ] (fun p => (‖p.1‖^2 : ℝ) • f p) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ w,ae_all_iff.mpr hw] with p hp hwp
  change (∑ i, w i) p = ∑ i, w i p at hp
  rw [hp]
  simp_rw [hwp]
  rw [← Finset.sum_smul,← EuclideanSpace.real_norm_sq_eq]

theorem radial_weight_bounded_multiplier_L2 {μ : Measure (Space κ)} {f : Space κ → ℂ}
    {a : Space κ → ℝ} (ha : AEStronglyMeasurable a μ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ p ∂μ, |a p| ≤ K) (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ i, w i =ᵐ[μ] (fun p => (p.1 i)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ, u =ᵐ[μ] (fun p => a p • ((‖p.1‖^2 : ℝ) • f p)) ∧
      ‖u‖ ≤ K*(∑ i, ‖w i‖) := by
  have hab : ∀ᵐ p ∂μ, ‖a p‖ ≤ K := by simpa only [Real.norm_eq_abs] using hbound
  have hatop : MemLp a ⊤ μ := memLp_top_of_bound ha K hab
  let W : Lp ℂ 2 μ := ∑ i, w i
  let u : Lp ℂ 2 μ := measureBoundedRealMul a hatop W
  refine ⟨u,?_,?_⟩
  · filter_upwards [measureBoundedRealMul_ae a hatop W,weightedCoordinateSum_ae w hw] with p hp hwp
    rw [hp]
    change a p • (∑ i, w i) p = _
    rw [hwp]
  · exact (measureBoundedRealMul_norm_le a hatop hab W).trans
      (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hK)

end TheoremT.Continuum.WeakGrushin
