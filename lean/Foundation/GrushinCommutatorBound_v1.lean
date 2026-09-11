import GrushinHoleCommutator_v1
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ksHoleCommutator_bound {φ : KSSpace × F → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ q,
      ‖ksHoleCommutator δ φ q‖ ≤ A/δ^2 := by
  obtain ⟨C1,hC1,h1⟩ := ksHole_derivative_bound
  obtain ⟨C2,hC2,h2⟩ := ksHole_secondDerivative_bound
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hex (k : Fin 4) : ∃ G : ℝ, ∀ q, ‖fderiv ℝ φ q (ksBasis k,0)‖ ≤ G :=
    (hc.fderiv_apply ℝ (ksBasis k,0)).exists_bound_of_continuous
      ((hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  choose G hG using hex
  have hG0 (k : Fin 4) : 0 ≤ G k := (norm_nonneg _).trans (hG k 0)
  refine ⟨∑ k : Fin 4,(C2*M+2*C1*G k),Finset.sum_nonneg (fun k _ => by have := hG0 k; positivity),fun δ hd hd1 q => ?_⟩
  rw [ksHoleCommutator,norm_neg]
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro k hk
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
  have ha := mul_le_mul (h2 δ hd q.1 k k) (hM q) (norm_nonneg _) (by positivity : 0 ≤ C2/δ^2)
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left (h1 δ hd q.1 k) (by norm_num : 0 ≤ (2:ℝ)))
    (hG k q) (norm_nonneg _) (by positivity : 0 ≤ 2*(C1/δ))
  apply (add_le_add ha hb).trans
  have hscale : δ ≤ 1 := hd1
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  field_simp
  nlinarith [mul_nonneg hC1 (hG0 k),mul_le_mul_of_nonneg_left hd1 (mul_nonneg hC1 (hG0 k))]

#print axioms ksHoleCommutator_bound
end TheoremT.Continuum
