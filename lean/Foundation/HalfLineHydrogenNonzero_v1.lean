import HalfLineHydrogenLp_v1

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem radialGround_ne_zero (Z r : ℝ) (hr : 0 < r) : radialGround Z r ≠ 0 := by
  unfold radialGround radialExp
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')

theorem halfLineMeasure_ne_zero : μ ≠ 0 := by
  intro h
  have hh := congrArg (fun ν : Measure ℝ => ν univ) h
  simpa [μ] using hh

theorem radialGroundL2_ne_zero (Z : ℝ) (hZ : 0 < Z) : radialGroundL2 Z hZ ≠ 0 := by
  intro hz
  haveI : NeZero μ := ⟨halfLineMeasure_ne_zero⟩
  have he : ∀ᵐ r ∂μ, radialGround Z r = 0 := by
    filter_upwards [radialGroundL2_coe Z hZ, Lp.coeFn_zero ℂ 2 μ] with r hr hr0
    rw [hz] at hr
    exact hr.symm.trans hr0
  obtain ⟨r, hr, hz⟩ := ((ae_restrict_mem measurableSet_Ioi).and he).exists
  exact radialGround_ne_zero Z r hr hz

theorem scalar_ground_profile_eq (Z r : ℝ) (c : ℂ) :
    (r*Real.exp (-Z*r)) • c = c * radialGround Z r := by
  simp [radialGround, radialExp, Complex.real_smul, mul_assoc, mul_comm, mul_left_comm]

#print axioms radialGroundL2_ne_zero
#print axioms scalar_ground_profile_eq
end TheoremT.HalfLine
