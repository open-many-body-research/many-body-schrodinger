import HalfLineTestPrimitive_v1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Zero weak derivative on the positive half-line implies an actual almost
everywhere constant. All smooth test functions are supplied by proved compact
primitives; neither a classical representative nor the conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

theorem halfline_test_smul_integrable {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun x => ψ x • f x) := by
  have hk : IntegrableOn f (tsupport ψ) := hf.integrableOn_compact_subset hs hc
  have hp : IntegrableOn (fun x => ψ x • f x) (tsupport ψ) :=
    hk.smul_of_top_right
      (hψ.memLp_top_of_hasCompactSupport hc (volume.restrict (tsupport ψ)))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hp
  intro x hx
  by_contra hnot
  exact hx (by simp [image_eq_zero_of_notMem_tsupport hnot])

theorem weak_derivative_zero_halfline_constant
    (f : ℝ → ℂ) (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi (0 : ℝ) → ∫ x, deriv ψ x • f x = 0) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ Ioi (0 : ℝ) → f x = c := by
  obtain ⟨η,hη,hηc,hηs,hηone⟩ := exists_halfline_unit_test
  let c : ℂ := ∫ x, η x • f x
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηfi := halfline_test_smul_integrable hf η hη.continuous hηc hηs
  have htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi (0 : ℝ) →
      ∫ x, ψ x • f x = (∫ x, ψ x) • c := by
    intro ψ hψ hψc hψs
    let t : ℝ := ∫ x, ψ x
    let χ : ℝ → ℝ := fun x => ψ x-t*η x
    have hχ : ContDiff ℝ ∞ χ := hψ.sub (contDiff_const.mul hη)
    have hχc : HasCompactSupport χ := hψc.sub (hηc.mul_left (f := fun _ => t))
    have hχs : tsupport χ ⊆ Ioi (0 : ℝ) :=
      (tsupport_sub ψ (fun x => t*η x)).trans
        (union_subset hψs (tsupport_mul_subset_right.trans hηs))
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hχzero : ∫ x, χ x = 0 := by
      dsimp only [χ]
      rw [integral_sub hψi (hηi.const_mul t),integral_const_mul,hηone]
      simp [t]
    obtain ⟨Φ,hΦ,hΦc,hΦs,hΦd⟩ := halfline_test_primitive χ hχ hχc hχs hχzero
    have hzero := hweak Φ hΦ hΦc hΦs
    rw [hΦd] at hzero
    have hψfi := halfline_test_smul_integrable hf ψ hψ.continuous hψc hψs
    change (∫ x, (ψ x-t*η x) • f x) = 0 at hzero
    simp_rw [sub_smul, mul_smul] at hzero
    have hti : Integrable (fun x => t • (η x • f x)) := hηfi.smul t
    rw [integral_sub hψfi hti, integral_smul] at hzero
    exact sub_eq_zero.mp hzero
  have hdiff : LocallyIntegrableOn (fun x => f x-c) (Ioi (0 : ℝ)) :=
    hf.sub (locallyIntegrableOn_const c)
  have hzero : ∀ᵐ x, x ∈ Ioi (0 : ℝ) → f x-c = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hdiff
    intro ψ hψ hψc hψs
    have hψfi := halfline_test_smul_integrable hf ψ hψ.continuous hψc hψs
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    simp_rw [smul_sub]
    rw [integral_sub hψfi (hψi.smul_const c),integral_smul_const,
      htest ψ hψ hψc hψs,sub_self]
  refine ⟨c,?_⟩
  filter_upwards [hzero] with x hx
  intro hxpos
  exact sub_eq_zero.mp (hx hxpos)

#print axioms halfline_test_smul_integrable
#print axioms weak_derivative_zero_halfline_constant
end TheoremT.OneDimensional
