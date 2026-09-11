import HalfLineRangeKernel_v1
import HalfLineFactorClosedRange_v1
import HalfLineHydrogenLp_v1
import HalfLineGroundWeakTest_v1

/-! Exact closed partner range for the actual half-line factors. The explicit
profile is used as an L² function; no unproved ground-profile domain membership
or adjoint-domain equality is required. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

theorem compact_B_ground_pairing (Z : ℝ) (hZ : 0 < Z) (φ : Test) :
    inner ℂ (B Z (testEmbed φ)) (radialGroundL2 Z hZ) = 0 := by
  have hψ : ContDiff ℝ ∞ (fun x => star (φ x)) := Complex.conjCLE.contDiff.comp φ.smooth
  have hdstar (x : ℝ) : deriv (fun y => star (φ y)) x = star (deriv (φ : ℝ→ℂ) x) :=
    (φ.smooth.differentiable (by simp) x).hasDerivAt.star.deriv
  have hψc : HasCompactSupport (fun x => star (φ x)) := φ.compact.comp_left (by simp)
  have hψs : tsupport (fun x => star (φ x)) ⊆ Ioi (0:ℝ) :=
    (tsupport_comp_subset (show star (0:ℂ) = 0 from star_zero _) (φ:ℝ→ℂ)).trans φ.support
  have hz := OneDimensional.radialGround_weak_test Z (fun x => star (φ x)) hψ hψc hψs
  have hi : (∫ x, (-deriv (fun y => star (φ y)) x - x⁻¹ • star (φ x) + Z • star (φ x)) *
      ((x * Real.exp (-Z*x) : ℝ) : ℂ) ∂μ) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hz
    · intro x hx
      have hn : x ∉ tsupport (φ : ℝ→ℂ) := fun hm => hx (φ.support hm)
      have hv := image_eq_zero_of_notMem_tsupport hn
      have hd := deriv_of_notMem_tsupport (f := (φ : ℝ→ℂ)) hn
      rw [hdstar]
      simp [hv, hd]
  rw [L2.inner_def]
  convert hi using 1
  apply integral_congr_ae
  have hb := B_coe Z (testEmbed φ)
  simp only [J_testEmbed, dJ_testEmbed] at hb
  filter_upwards [hb, φ.coe_value, φ.coe_gradient, radialGroundL2_coe Z hZ] with x hb hv hd hg
  rw [hb, hv, hd, hg]
  rw [hdstar]
  simp [RCLike.inner_apply, radialGround, radialExp, star_add, star_sub,
    star_neg, star_smul, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc]

theorem ground_mem_range_orthogonal (Z : ℝ) (hZ : 0 < Z) :
    radialGroundL2 Z hZ ∈ (B Z).range.orthogonal := by
  rintro _ ⟨u,rfl⟩
  refine testEmbed_dense.induction_on
    (p := fun v => inner ℂ (B Z v) (radialGroundL2 Z hZ) = 0) u ?_ ?_
  · exact isClosed_eq ((B Z).continuous.inner continuous_const) continuous_const
  · exact compact_B_ground_pairing Z hZ

theorem range_orthogonal_eq_ground_span (Z : ℝ) (hZ : 0 < Z) :
    (B Z).range.orthogonal = Submodule.span ℂ {radialGroundL2 Z hZ} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨c,hc⟩ := range_orthogonal_profile hf
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    apply Lp.ext
    filter_upwards [hc, Lp.coeFn_smul c (radialGroundL2 Z hZ), radialGroundL2_coe Z hZ]
      with x hx hs hg
    simp only [Pi.smul_apply] at hs
    rw [hs,hg,hx]
    simp [radialGround, radialExp, Complex.real_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  · apply Submodule.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]
    exact ground_mem_range_orthogonal Z hZ

theorem range_B_exact (Z : ℝ) (hZ : 0 < Z) :
    (B Z).range = (Submodule.span ℂ {radialGroundL2 Z hZ}).orthogonal := by
  rw [← range_orthogonal_eq_ground_span Z hZ,
    Submodule.orthogonal_orthogonal_eq_closure, B_range_closed hZ]

#print axioms compact_B_ground_pairing
#print axioms ground_mem_range_orthogonal
#print axioms range_orthogonal_eq_ground_span
#print axioms range_B_exact
end TheoremT.HalfLine
