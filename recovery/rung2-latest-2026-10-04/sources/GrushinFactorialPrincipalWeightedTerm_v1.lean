import GrushinFactorialPrincipalComponentL2_v1

/-! Multiplicity-weighted R15 components, including zero multiplicities.
No inaccessible derivative representative is requested for a vanished term. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
set_option maxRecDepth 4096

theorem factorial_principal_one_hit_weighted_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (i : Fin 4) (j : Fin 3) :
    ∃ U : Lp ℂ 2 μ,
      U =ᵐ[μ] (fun p => (α i : ℝ) • (p.1 i •
        d (fun l => α l-(Pi.single i 1 : Fin 4 → ℕ) l) (β+Pi.single j 2) p)) ∧
      ‖U‖ ≤ (α i : ℝ)*N := by
  by_cases hi : 1 ≤ α i
  · obtain ⟨u,hu,hun⟩ := factorial_principal_one_hit_component_L2 d W r N hW hN α β hc i j hi
    refine ⟨(α i : ℝ) • u,?_,?_⟩
    · filter_upwards [Lp.coeFn_smul (α i : ℝ) u,hu] with p hp hpu
      rw [hp]
      change (α i : ℝ) • u p = _
      rw [hpu]
    · rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hun (Nat.cast_nonneg _)
  · have hzero : α i = 0 := by omega
    refine ⟨0,?_,?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 μ] with p hp
      simpa only [hzero,Nat.cast_zero,zero_smul,Pi.zero_apply] using hp
    · simp [hzero]

theorem factorial_principal_two_hit_weighted_L2 {μ : Measure (Space (Fin 3))}
    (d : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℝ)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → FactorialShiftedOuterL2Rep d W a b)
    (hN : ∀ a b, factorialMultiDerivativeCost a b ≤ r-2 → factorialOuterNorm (W a b) ≤ N)
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) (hc : factorialMultiDerivativeCost α β ≤ r)
    (i : Fin 4) (j : Fin 3) :
    ∃ U : Lp ℂ 2 μ,
      U =ᵐ[μ] (fun p => ((α i*(α i-1) : ℕ) : ℝ) •
        d (fun l => α l-(Pi.single i 2 : Fin 4 → ℕ) l) (β+Pi.single j 2) p) ∧
      ‖U‖ ≤ ((α i*(α i-1) : ℕ) : ℝ)*N := by
  by_cases hi : 2 ≤ α i
  · obtain ⟨u,hu,hun⟩ := factorial_principal_two_hit_component_L2 d W r N hW hN α β hc i j hi
    refine ⟨((α i*(α i-1) : ℕ) : ℝ) • u,?_,?_⟩
    · filter_upwards [Lp.coeFn_smul ((α i*(α i-1) : ℕ) : ℝ) u,hu] with p hp hpu
      rw [hp]
      change ((α i*(α i-1) : ℕ) : ℝ) • u p = _
      rw [hpu]
    · rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hun (Nat.cast_nonneg _)
  · have hzero : α i*(α i-1) = 0 := by
      have hval : α i = 0 ∨ α i = 1 := by omega
      rcases hval with h | h <;> simp [h]
    refine ⟨0,?_,?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 μ] with p hp
      simpa only [hzero,Nat.cast_zero,zero_smul,Pi.zero_apply] using hp
    · simp [hzero]

end TheoremT.Continuum.WeakGrushin
