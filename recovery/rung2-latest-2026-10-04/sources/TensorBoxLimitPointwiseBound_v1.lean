import TensorBoxContinuousRepresentative_v1
import SmoothCoordinateSubsetFields7_v1

/-! Quantitative pointwise estimates pass to the actual strong L2/uniform
limits. The final constant uses the limiting L2 norms, with no mollification
loss and no prior pointwise bound on the limit. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem tensor_box7_pointwise_bound_of_L2_limits
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (D : ℕ → Finset (Fin 7) → (Fin 7 → ℝ) → ℂ)
    (hD : ∀ n s, ContinuousOn (D n s) (tensorClosedBox7 a b))
    (hd : ∀ n s i, i ∉ s → ∀ x ∈ tensorClosedBox7 a b,
      HasDerivAt (fun r => D n s (Function.update x i r)) (D n (insert i s) x) (x i))
    (V : ℕ → Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hV : ∀ n s, (V n s : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict (tensorClosedBox7 a b)] D n s)
    (W : Finset (Fin 7) → Lp ℂ 2 (volume.restrict (tensorClosedBox7 a b)))
    (hW : ∀ s, Tendsto (fun n => V n s) atTop (𝓝 (W s)))
    {g : (Fin 7 → ℝ) → ℂ}
    (hg : TendstoUniformlyOn (fun n => D n ∅) g atTop (tensorClosedBox7 a b))
    {M : ℝ} (hM : 0 ≤ M) (hWM : ∀ s, ‖W s‖ ≤ M)
    {x : Fin 7 → ℝ} (hx : x ∈ tensorClosedBox7 a b) :
    ‖g x‖ ≤ boxEvaluationConstant a b * M := by
  have hE : 0 < boxEvaluationConstant a b := boxEvaluationConstant_pos hab
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / boxEvaluationConstant a b
  have hδ : 0 < δ := div_pos hε hE
  have hevent : ∀ s, ∀ᶠ n in atTop, ‖V n s‖ ≤ M+δ := by
    intro s
    exact ((hW s).norm).eventually_le_const (lt_of_le_of_lt (hWM s) (lt_add_of_pos_right M hδ))
  have hbd : ‖g x‖ ≤ boxEvaluationConstant a b * (M+δ) := by
    apply le_of_tendsto ((hg.tendsto_at hx).norm)
    filter_upwards [Filter.eventually_all.mpr hevent] with n hn
    apply tensor_box7_pointwise_geometric_bound hab (hD n) (hd n) (by linarith) ?_ hx
    intro s
    rw [tensor_box_sqrt_integral_eq_Lp_norm (V n s) (hV n s)]
    exact hn s
  have heq : boxEvaluationConstant a b * (M+δ) = boxEvaluationConstant a b * M + ε := by
    dsimp only [δ]
    field_simp
  exact heq ▸ hbd

end TheoremT.Continuum
