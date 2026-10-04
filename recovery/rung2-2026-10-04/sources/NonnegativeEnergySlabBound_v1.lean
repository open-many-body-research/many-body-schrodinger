import Mathlib.Tactic

/-! Scalar cancellation used after the actual slab and energy estimates.
Zero energy is handled without dividing by the input norm or energy. -/
namespace TheoremT.Continuum

theorem nonnegative_energy_slab_bounds (I D P K : ℝ)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hslab : I ≤ K*D) (hcs : D^2 ≤ I*P) :
    I ≤ K^2*P ∧ D ≤ K*P := by
  have hd : D ≤ K*P := by
    by_cases hz : D = 0
    · rw [hz]
      exact mul_nonneg hK hP
    · have hp : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hp).mp
      calc
        D*D = D^2 := (pow_two D).symm
        _ ≤ I*P := hcs
        _ ≤ (K*D)*P := mul_le_mul_of_nonneg_right hslab hP
        _ = D*(K*P) := by ring
  refine ⟨?_,hd⟩
  calc
    I ≤ K*D := hslab
    _ ≤ K*(K*P) := mul_le_mul_of_nonneg_left hd hK
    _ = K^2*P := by ring

end TheoremT.Continuum
