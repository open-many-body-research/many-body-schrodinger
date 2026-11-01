import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The two analytic coefficients of f(t)+|t|g(t)=0 are individually zero
on a symmetric interval. Both sides of the singular point are essential.
This is a one-dimensional uniqueness prerequisite for physical KS germs. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace TheoremT.Continuum

theorem analytic_absolute_value_decomposition_zero
    {f g : ℝ → ℂ} {r : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℝ f (Ioo (-r) r))
    (hg : AnalyticOnNhd ℝ g (Ioo (-r) r))
    (hfg : ∀ t ∈ Ioo (-r) r, f t + |t| • g t = 0) :
    EqOn f 0 (Ioo (-r) r) ∧ EqOn g 0 (Ioo (-r) r) := by
  have ha : r/2 ∈ Ioo (-r) r := by constructor <;> linarith
  have hb : -(r/2) ∈ Ioo (-r) r := by constructor <;> linarith
  have hpos : ∀ᶠ t : ℝ in 𝓝 (r/2), t ∈ Ioo 0 r :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hneg : ∀ᶠ t : ℝ in 𝓝 (-(r/2)), t ∈ Ioo (-r) 0 :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hplus : EqOn (fun t => f t + t • g t) 0 (Ioo (-r) r) := by
    apply (hf.add (analyticOnNhd_id.smul hg)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_Ioo ha
    filter_upwards [hpos] with t ht
    have hi : t ∈ Ioo (-r) r := ⟨by linarith [ht.1],ht.2⟩
    simpa only [abs_of_pos ht.1,Pi.add_apply,Pi.zero_apply] using hfg t hi
  have hminus : EqOn (fun t => f t - t • g t) 0 (Ioo (-r) r) := by
    apply (hf.sub (analyticOnNhd_id.smul hg)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_Ioo hb
    filter_upwards [hneg] with t ht
    have hi : t ∈ Ioo (-r) r := ⟨ht.1,by linarith [ht.2]⟩
    simpa only [abs_of_neg ht.2,neg_smul,sub_eq_add_neg,Pi.add_apply,Pi.neg_apply,Pi.zero_apply]
      using hfg t hi
  have hg0 : EqOn g 0 (Ioo (-r) r) := by
    apply hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo ha
    filter_upwards [hpos] with t ht
    have hi : t ∈ Ioo (-r) r := ⟨by linarith [ht.1],ht.2⟩
    have hp := hplus hi
    have hm := hminus hi
    have htg : (t : ℂ)*g t=0 := by
      simp only [Complex.real_smul] at hp hm
      linear_combination (1/2 : ℂ)*hp - (1/2 : ℂ)*hm
    exact (mul_eq_zero.mp htg).resolve_left (Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1))
  refine ⟨?_,hg0⟩
  intro t ht
  have h := hplus ht
  simpa only [hg0 ht,Pi.zero_apply,smul_zero,add_zero] using h

end TheoremT.Continuum
