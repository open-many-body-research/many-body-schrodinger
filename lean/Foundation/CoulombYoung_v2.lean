import SpinCoulombNorm_v2

noncomputable section

namespace TheoremT.Continuum

/-- Weighted Young interpolation, including zero gradient and zero coefficient.
This arithmetic lemma will be applied to genuine weak derivative energies. -/
theorem coulomb_young_numeric {C A B D ε : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε)
    (hD : D ≤ A * B) :
    C * Real.sqrt D ≤ ε * B + C^2 / (4 * ε) * A := by
  calc
    C * Real.sqrt D ≤ C * Real.sqrt (A * B) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hD) hC
    _ = C * (Real.sqrt A * Real.sqrt B) := by rw [Real.sqrt_mul hA]
    _ ≤ ε * B + C^2 / (4 * ε) * A := by
      have hquad := sq_nonneg (C * Real.sqrt A - 2 * ε * Real.sqrt B)
      simp only [sub_sq, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB] at hquad
      have hden : (4 * ε) * (ε * B + C^2 / (4 * ε) * A) =
          4 * ε^2 * B + C^2 * A := by
        field_simp [hε.ne']
      apply (mul_le_mul_iff_of_pos_left (show 0 < 4 * ε by positivity)).mp
      rw [hden]
      nlinarith

#print axioms coulomb_young_numeric

end TheoremT.Continuum
