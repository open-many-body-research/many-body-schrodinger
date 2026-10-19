import WeakGrushinPotentialForcingPointwise_v1
import GrushinLocalPotentialL2_v1

/-! Integrated finite-family potential forcing estimates for arbitrary
measures. Membership and square-integrability are proved before comparison
of the actual Bochner integrals. The aggregate coefficient bound is used
before integration, so no component-count factor is introduced.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem potential_forcing_integral_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι]
    (B : α → ℝ) (A : ι → α → ℝ) (G : α → ℂ) (d : ι → α → ℂ)
    (hB : MemLp B ⊤ μ) (hA : ∀ j, MemLp (A j) ⊤ μ)
    (hG : MemLp G 2 μ) (hd : ∀ j, MemLp (d j) 2 μ)
    {b b1 : ℝ} (hb : ∀ᵐ x ∂μ, |B x| ≤ b)
    (hb1 : ∀ᵐ x ∂μ, (∑ j, |A j x|^2) ≤ b1^2) :
    MemLp (fun x => B x • G x) 2 μ ∧
    (∀ j, MemLp (fun x => -(A j x • G x) - B x • d j x) 2 μ) ∧
    Integrable (fun x => ‖B x • G x‖^2) μ ∧
    (∀ j, Integrable (fun x => ‖-(A j x • G x) - B x • d j x‖^2) μ) ∧
    (∫ x, ‖B x • G x‖^2 ∂μ) ≤ b^2*(∫ x, ‖G x‖^2 ∂μ) ∧
    (∑ j, ∫ x, ‖-(A j x • G x) - B x • d j x‖^2 ∂μ) ≤
      2*b1^2*(∫ x, ‖G x‖^2 ∂μ) + 2*b^2*(∑ j, ∫ x, ‖d j x‖^2 ∂μ) := by
  have hBG : MemLp (fun x => B x • G x) 2 μ := hG.smul hB
  have hForce (j : ι) : MemLp (fun x => -(A j x • G x) - B x • d j x) 2 μ :=
    (hG.smul (hA j)).neg.sub ((hd j).smul hB)
  have hGsq : Integrable (fun x => ‖G x‖^2) μ := hG.integrable_norm_pow (by norm_num)
  have hdsq (j : ι) : Integrable (fun x => ‖d j x‖^2) μ :=
    (hd j).integrable_norm_pow (by norm_num)
  have hBGsq : Integrable (fun x => ‖B x • G x‖^2) μ := hBG.integrable_norm_pow (by norm_num)
  have hFsq (j : ι) : Integrable (fun x => ‖-(A j x • G x) - B x • d j x‖^2) μ :=
    (hForce j).integrable_norm_pow (by norm_num)
  have hdsum : Integrable (fun x => ∑ j, ‖d j x‖^2) μ :=
    integrable_finsetSum _ (fun j _ => hdsq j)
  refine ⟨hBG,hForce,hBGsq,hFsq,?_,?_⟩
  · calc
      _ ≤ ∫ x, b^2*‖G x‖^2 ∂μ := by
        apply integral_mono_ae hBGsq (hGsq.const_mul (b^2))
        filter_upwards [hb] with x hx
        exact potential_smul_norm_sq_le (G x) hx
      _ = _ := integral_const_mul _ _
  · have hm : (∫ x, ∑ j, ‖-(A j x • G x) - B x • d j x‖^2 ∂μ) ≤
        ∫ x, 2*b1^2*‖G x‖^2 + 2*b^2*(∑ j, ‖d j x‖^2) ∂μ := by
      apply integral_mono_ae (integrable_finsetSum _ (fun j _ => hFsq j))
        ((hGsq.const_mul (2*b1^2)).fun_add (hdsum.const_mul (2*b^2)))
      filter_upwards [hb,hb1] with x hx hy
      exact potential_spectator_forcing_sum_norm_sq_le (fun j => A j x) (G x) (fun j => d j x) hx hy
    rw [integral_finsetSum _ (fun j _ => hFsq j),
      integral_add (hGsq.const_mul (2*b1^2)) (hdsum.const_mul (2*b^2)),
      integral_const_mul,integral_const_mul,integral_finsetSum _ (fun j _ => hdsq j)] at hm
    exact hm

#print axioms potential_forcing_integral_bounds
end TheoremT.Continuum.WeakGrushin
