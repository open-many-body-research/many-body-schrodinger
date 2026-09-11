import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! A domain-faithful partner-gap transfer. The complete space D may be an
actual Sobolev domain with its own norm, while J gives its values in E. The
bound in the D norm proves closedness of the partner range. The integration
by parts and orthogonal-range identity are explicit physical prerequisites. -/
noncomputable section
namespace TheoremT.OperatorTheory
variable {D E : Type*}
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem partner_gap_transfer
    (J A B : D →L[ℂ] E) (K c : ℝ) (hK : 0 < K) (hc : 0 < c)
    (hcomplete_bound : ∀ v : D, ‖v‖ ≤ K * ‖B v‖)
    (hvalue_bound : ∀ v : D, c * ‖J v‖ ≤ ‖B v‖)
    (hibp : ∀ u v : D, inner ℂ (A u) (J v) = inner ℂ (J u) (B v))
    (g : E) (horth : B.range.orthogonal = Submodule.span ℂ {g})
    (u : D) (hu : inner ℂ g (J u) = 0) :
    c * ‖J u‖ ≤ ‖A u‖ := by
  have hanti : AntilipschitzWith (⟨K,hK.le⟩ : NNReal) B :=
    B.antilipschitz_of_bound hcomplete_bound
  have hclosed : B.range.topologicalClosure = B.range :=
    ContinuousLinearMap.closed_range_of_antilipschitz hanti
  have hrange : B.range = (Submodule.span ℂ {g}).orthogonal := by
    calc
      B.range = B.range.topologicalClosure := hclosed.symm
      _ = B.range.orthogonal.orthogonal :=
        B.range.orthogonal_orthogonal_eq_closure.symm
      _ = (Submodule.span ℂ {g}).orthogonal := by rw [horth]
  have hum : J u ∈ B.range := by
    rw [hrange]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hu
  obtain ⟨v,hv⟩ := hum
  have hv' : B v = J u := hv
  have hp : ‖J u‖^2 = (inner ℂ (A u) (J v)).re := by
    rw [hibp,hv',inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hsq : ‖J u‖^2 ≤ ‖A u‖ * ‖J v‖ := by
    rw [hp]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hvb := hvalue_bound v
  rw [hv'] at hvb
  by_cases hz : ‖J u‖ = 0
  · simp only [hz,mul_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖J u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hm := mul_le_mul_of_nonneg_left hsq hc.le
  have hn := mul_le_mul_of_nonneg_left hvb (norm_nonneg (A u))
  have hfinal : (c * ‖J u‖) * ‖J u‖ ≤ ‖A u‖ * ‖J u‖ := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hpos).mp hfinal

#print axioms partner_gap_transfer
end TheoremT.OperatorTheory
