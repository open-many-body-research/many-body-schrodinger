import HalfLineHardyExtension_v1
import HalfLineQuotientClosed_v1

/-! The bounded domain multiplier W is the actual reciprocal-coordinate
multiplication in the half-line L² quotient. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine
open HalfLineCompactHardy

theorem W_coe (u : D) : (W u : ℝ → ℂ) =ᵐ[μ] fun x => x⁻¹ • J u x := by
  obtain ⟨f,hf⟩ := exists_test_sequence u
  apply quotient_of_tendsto (J.continuous.tendsto u |>.comp hf)
    (W.continuous.tendsto u |>.comp hf)
  intro n
  simp only [Function.comp_apply]
  rw [W_testEmbed, J_testEmbed]
  filter_upwards [(f n).coe_quotientLp, (f n).coe_value] with x hx hy
  rw [hx, hy]
  rfl

theorem domain_quotient_memLp (u : D) : MemLp (fun x => x⁻¹ • J u x) 2 μ :=
  MemLp.ae_eq (W_coe u) (Lp.memLp (W u))

theorem W_eq_actual_toLp (u : D) :
    W u = (domain_quotient_memLp u).toLp (fun x => x⁻¹ • J u x) := by
  apply Lp.ext
  exact (W_coe u).trans (domain_quotient_memLp u).coeFn_toLp.symm

theorem actual_hardy_domain (u : D) :
    ‖(domain_quotient_memLp u).toLp (fun x => x⁻¹ • J u x)‖ ≤ 2 * ‖dJ u‖ := by
  rw [← W_eq_actual_toLp]
  exact hardy_domain u

#print axioms W_coe
#print axioms domain_quotient_memLp
#print axioms W_eq_actual_toLp
#print axioms actual_hardy_domain
end TheoremT.HalfLine
