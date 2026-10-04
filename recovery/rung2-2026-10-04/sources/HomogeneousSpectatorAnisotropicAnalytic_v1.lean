import SpectatorScalingMap_v1

/-! Joint analyticity on the full separate radial/spectator domains. Actual
block rescaling retains the two rates; no isotropic-radius loss is hidden.
The target is the original double-index sum of the specified polynomials. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem exists_positive_larger_geometric_radius {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 ≤ r) (hDr : D*r < 1) :
    ∃ a : ℝ, 0 < a ∧ r < a ∧ D*a < 1 := by
  by_cases hD0 : D = 0
  · exact ⟨r+1,by linarith,by linarith,by simp [hD0]⟩
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    have hri : r < 1/D := (lt_div_iff₀ hDp).mpr (by simpa [mul_comm] using hDr)
    obtain ⟨a,hra,haD⟩ := exists_between hri
    exact ⟨a,hr.trans_lt hra,hra,by simpa [mul_comm] using (lt_div_iff₀ hDp).mp haD⟩

theorem homogeneous_spectator_sum_analytic_anisotropic {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) {M D S : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i)) :
    AnalyticOnNhd ℂ (homogeneousSpectatorSum A)
      {z : Fin 3 ⊕ Fin d → ℂ |
        D*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧
        S*‖fun i : Fin d => z (.inr i)‖ < 1} := by
  intro z hz
  obtain ⟨a,ha,hza,hDa⟩ := exists_positive_larger_geometric_radius hD (norm_nonneg _) hz.1
  obtain ⟨b,hb,hzb,hSb⟩ := exists_positive_larger_geometric_radius hS (norm_nonneg _) hz.2
  let T := max (D*a) (S*b)
  have hT : 0 ≤ T := (mul_nonneg hD ha.le).trans (le_max_left _ _)
  have hT1 : T < 1 := max_lt hDa hSb
  let A' := rescaledHomogeneousSpectatorFamily A a b
  have hA' : ∀ m γ, (A' m γ).IsHomogeneous m :=
    rescaledHomogeneousSpectatorFamily_isHomogeneous A hA a b
  have hL' : ∀ m γ, polynomialCoeffL1 (A' m γ) ≤ M*T^(m+∑ i : Fin d, γ i) :=
    polynomialCoeffL1_rescaledHomogeneousSpectatorFamily A hM hD hS ha.le hb.le
      (le_max_left _ _) (le_max_right _ _) hL
  let w := spectatorScalingMap a⁻¹ b⁻¹ z
  have hw : ‖w‖ ≤ 1 := spectatorScalingMap_inverse_norm_le_one ha hb z
    (fun i => (norm_le_pi_norm _ i).trans hza.le)
    (fun i => (norm_le_pi_norm _ i).trans hzb.le)
  have hTw : T*‖w‖ < 1 := by
    calc
      _ ≤ T*1 := mul_le_mul_of_nonneg_left hw hT
      _ = T := mul_one T
      _ < 1 := hT1
  have hf := homogeneous_spectator_sum_analytic_isotropic A' hA' hM hT hL' w hTw
  have hcomp : AnalyticAt ℂ
      (fun v => homogeneousSpectatorSum A' (spectatorScalingMap a⁻¹ b⁻¹ v)) z := by
    exact AnalyticAt.comp_of_eq (g := homogeneousSpectatorSum A') hf
      (spectatorScalingMap_analyticAt a⁻¹ b⁻¹ z) rfl
  have heq : (fun v => homogeneousSpectatorSum A' (spectatorScalingMap a⁻¹ b⁻¹ v)) =
      homogeneousSpectatorSum A := by
    funext v
    rw [homogeneousSpectatorSum_rescaling A hA a b,
      spectatorScalingMap_inverse_cancel (ne_of_gt ha) (ne_of_gt hb)]
  exact heq ▸ hcomp

end TheoremT.Continuum
