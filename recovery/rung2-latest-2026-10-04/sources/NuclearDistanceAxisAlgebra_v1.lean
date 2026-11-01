import NuclearDistanceAxisMap_v1

/-! Exact squared-distance reconstruction for the literal complex rational
nuclear map. These are algebraic identities, without any square-root or
planar-representative choice. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

theorem nuclearDistanceAxisZ_mul (q : Fin 3 → ℂ) (hs : q 1 ≠ 0) :
    (2 * q 1) * nuclearDistanceAxisZ q = (q 0)^2 + (q 1)^2 - (q 2)^2 := by
  exact mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hs)

theorem nuclearDistanceAxisW_add_Z_sq (q : Fin 3 → ℂ) :
    nuclearDistanceAxisW q + (nuclearDistanceAxisZ q)^2 = (q 0)^2 := by
  simp only [nuclearDistanceAxisW, sub_add_cancel]

theorem nuclearDistanceAxisW_add_shifted_Z_sq (q : Fin 3 → ℂ) (hs : q 1 ≠ 0) :
    nuclearDistanceAxisW q + (nuclearDistanceAxisZ q - q 1)^2 = (q 2)^2 := by
  have hz := nuclearDistanceAxisZ_mul q hs
  dsimp only [nuclearDistanceAxisW]
  linear_combination -hz

end TheoremT.Continuum
