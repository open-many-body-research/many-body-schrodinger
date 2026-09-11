import HalfLineHardyFaithful_v1

/-! Compact integration identities extended to every member of the declared
half-line domain. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem domain_value_gradient_real_zero (u : D) : inner ℝ (J u) (dJ u) = 0 := by
  refine testEmbed_dense.induction_on
    (p := fun v => inner ℝ (J v) (dJ v) = 0) u ?_ ?_
  · exact isClosed_eq (J.continuous.inner dJ.continuous) continuous_const
  · intro f
    exact f.value_gradient_real_zero

theorem domain_quotient_gradient_real (u : D) :
    2 * inner ℝ (W u) (dJ u) = ‖W u‖^2 := by
  refine testEmbed_dense.induction_on
    (p := fun v => 2 * inner ℝ (W v) (dJ v) = ‖W v‖^2) u ?_ ?_
  · exact isClosed_eq (continuous_const.mul (W.continuous.inner dJ.continuous))
      (W.continuous.norm.pow 2)
  · intro f
    rw [W_testEmbed, dJ_testEmbed]
    exact f.quotient_gradient_real

theorem domain_derivative_pairing (u v : D) :
    inner ℂ (dJ u) (J v) = -inner ℂ (J u) (dJ v) := by
  refine testEmbed_dense.induction_on₂
    (p := fun u v => inner ℂ (dJ u) (J v) = -inner ℂ (J u) (dJ v)) ?_ ?_ u v
  · exact isClosed_eq ((dJ.continuous.comp continuous_fst).inner (J.continuous.comp continuous_snd))
      (((J.continuous.comp continuous_fst).inner (dJ.continuous.comp continuous_snd)).neg)
  · intro f g
    have h := f.pair_ibp g
    change inner ℂ f.gradient g.value = -inner ℂ f.value g.gradient
    rw [h, neg_neg]

theorem domain_quotient_pairing (u v : D) :
    inner ℂ (W u) (J v) = inner ℂ (J u) (W v) := by
  refine testEmbed_dense.induction_on₂
    (p := fun u v => inner ℂ (W u) (J v) = inner ℂ (J u) (W v)) ?_ ?_ u v
  · exact isClosed_eq ((W.continuous.comp continuous_fst).inner (J.continuous.comp continuous_snd))
      ((J.continuous.comp continuous_fst).inner (W.continuous.comp continuous_snd))
  · intro f g
    rw [W_testEmbed, W_testEmbed, J_testEmbed, J_testEmbed]
    exact f.quotient_pair_symmetry g

#print axioms domain_value_gradient_real_zero
#print axioms domain_quotient_gradient_real
#print axioms domain_derivative_pairing
#print axioms domain_quotient_pairing
end TheoremT.HalfLine
