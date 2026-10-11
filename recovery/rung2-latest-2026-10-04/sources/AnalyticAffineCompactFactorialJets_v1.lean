import AnalyticCompactFactorialBound_v1
import SmoothAffineCompactFiniteJets_v1

/-! All-order bounds for actual analytic affine families, uniformly in a real
parameter in [0,1]. The scaled coefficient retains its small parameter.
Constants precede the parameter, point, derivative order, and source amplitude.
The constants are existential; this theorem does not evaluate them. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem analytic_affine_compact_factorial_source_bound
    {f0 f1 : X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf0 : AnalyticOnNhd ℝ f0 K) (hf1 : AnalyticOnNhd ℝ f1 K) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ k : ℕ, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ ≤
          C * A^k * (k.factorial : ℝ) ∧
        ‖iteratedFDeriv ℝ k (fun q => eps * (f0 q + eps * f1 q)) x‖ ≤
          eps * (C * A^k * (k.factorial : ℝ)) ∧
        ∀ a0 : ℂ,
          ‖iteratedFDeriv ℝ k (fun q => (f0 q + eps * f1 q) • a0) x‖ ≤
            (C * A^k * (k.factorial : ℝ)) * ‖a0‖ := by
  obtain ⟨C0,A0,hC0,hA0,hb0⟩ := analyticOnNhd_compact_factorial_bound hK hf0
  obtain ⟨C1,A1,hC1,hA1,hb1⟩ := analyticOnNhd_compact_factorial_bound hK hf1
  have hC0p : 0 ≤ C0 := by linarith
  have hC1p : 0 ≤ C1 := by linarith
  have hA0p : 0 ≤ A0 := by linarith
  have hA1p : 0 ≤ A1 := by linarith
  refine ⟨C0+C1,A0+A1,by linarith,by linarith,?_⟩
  intro eps heps0 heps1 k x hx
  have h0 : ContDiffAt ℝ k f0 x := (hf0 x hx).contDiffAt
  have h1 : ContDiffAt ℝ k f1 x := (hf1 x hx).contDiffAt
  have ha : ContDiffAt ℝ k (fun q => f0 q + eps * f1 q) x := by
    simpa only [smul_eq_mul] using h0.add (h1.const_smul eps)
  have h1eps : ContDiffAt ℝ k (eps • f1) x := h1.const_smul eps
  have heps : ‖eps‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg heps0]
  have hp0 : A0^k ≤ (A0+A1)^k := pow_le_pow_left₀ hA0p (by linarith) k
  have hp1 : A1^k ≤ (A0+A1)^k := pow_le_pow_left₀ hA1p (by linarith) k
  have b0 : ‖iteratedFDeriv ℝ k f0 x‖ ≤ C0*(A0+A1)^k*(k.factorial : ℝ) :=
    (hb0 x hx k).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp0 hC0p) (Nat.cast_nonneg _))
  have b1 : ‖iteratedFDeriv ℝ k f1 x‖ ≤ C1*(A0+A1)^k*(k.factorial : ℝ) :=
    (hb1 x hx k).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp1 hC1p) (Nat.cast_nonneg _))
  have hb : ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ ≤
      (C0+C1)*(A0+A1)^k*(k.factorial : ℝ) := by
    change ‖iteratedFDeriv ℝ k (f0 + eps • f1) x‖ ≤ _
    rw [iteratedFDeriv_add_apply h0 h1eps,
      iteratedFDeriv_const_smul_apply h1]
    calc
      ‖iteratedFDeriv ℝ k f0 x + eps • iteratedFDeriv ℝ k f1 x‖ ≤
          ‖iteratedFDeriv ℝ k f0 x‖ + ‖eps • iteratedFDeriv ℝ k f1 x‖ := norm_add_le _ _
      _ = ‖iteratedFDeriv ℝ k f0 x‖ + ‖eps‖ * ‖iteratedFDeriv ℝ k f1 x‖ := by rw [norm_smul]
      _ ≤ C0*(A0+A1)^k*(k.factorial : ℝ) + 1*(C1*(A0+A1)^k*(k.factorial : ℝ)) :=
        add_le_add b0 (mul_le_mul heps b1 (norm_nonneg _) (by norm_num))
      _ = (C0+C1)*(A0+A1)^k*(k.factorial : ℝ) := by ring
  refine ⟨hb,?_,?_⟩
  · change ‖iteratedFDeriv ℝ k (eps • (fun q => f0 q + eps * f1 q)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply ha,norm_smul,Real.norm_eq_abs,abs_of_nonneg heps0]
    exact mul_le_mul_of_nonneg_left hb heps0
  · intro a0
    rw [iteratedFDeriv_smul_const_apply ha]
    calc
      ‖((ContinuousLinearMap.id ℝ ℝ).smulRight a0).compContinuousMultilinearMap
          (iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x)‖ ≤
          ‖(ContinuousLinearMap.id ℝ ℝ).smulRight a0‖ *
            ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ = ‖a0‖ * ‖iteratedFDeriv ℝ k (fun q => f0 q + eps * f1 q) x‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_id,one_mul]
      _ ≤ ‖a0‖ * ((C0+C1)*(A0+A1)^k*(k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = ((C0+C1)*(A0+A1)^k*(k.factorial : ℝ)) * ‖a0‖ := mul_comm _ _

end TheoremT.Continuum
