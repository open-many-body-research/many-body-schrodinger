import SpectatorScalingContinuousLinearMap_v1
import IteratedFDerivLinearCompositionAt_v1

/-! Coordinate-word evaluation of the iterated derivative after the
actual block scaling. Every spatial direction contributes its own a,
and every spectator direction its own b. The local smoothness hypothesis
is explicit. These identities do not replace the directional factors by
the maximum scale or assume an unproved coordinate-derivative bound. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

theorem spectatorScaling_iteratedFDeriv_word
    (a b : ℝ) (f : (Fin 3 ⊕ Fin d → ℂ) → ℂ)
    (z : Fin 3 ⊕ Fin d → ℂ) (n : ℕ) (w : Fin n → Fin 3 ⊕ Fin d)
    (hf : ContDiffAt ℂ n f (spectatorScalingMap a b z)) :
    iteratedFDeriv ℂ n (f ∘ spectatorScalingMap a b) z
        (fun j => Pi.single (w j) (1 : ℂ)) =
      (∏ j, spectatorScalingCoefficient a b (w j)) *
        iteratedFDeriv ℂ n f (spectatorScalingMap a b z)
          (fun j => Pi.single (w j) (1 : ℂ)) := by
  rw [← spectatorScalingContinuousLinearMap_coe a b] at hf ⊢
  rw [iteratedFDeriv_comp_right_of_contDiffAt _ _ _ _ hf,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [spectatorScalingContinuousLinearMap_single]
  simpa only [smul_eq_mul] using
    (iteratedFDeriv ℂ n f (spectatorScalingContinuousLinearMap a b z)).map_smul_univ
      (fun j => spectatorScalingCoefficient a b (w j))
      (fun j => Pi.single (w j) (1 : ℂ))

theorem spectatorScaling_iteratedFDeriv_word_norm_le
    (a b : ℝ) (f : (Fin 3 ⊕ Fin d → ℂ) → ℂ)
    (z : Fin 3 ⊕ Fin d → ℂ) (n : ℕ) (w : Fin n → Fin 3 ⊕ Fin d)
    (hf : ContDiffAt ℂ n f (spectatorScalingMap a b z)) :
    ‖iteratedFDeriv ℂ n (f ∘ spectatorScalingMap a b) z
        (fun j => Pi.single (w j) (1 : ℂ))‖ ≤
      ‖iteratedFDeriv ℂ n f (spectatorScalingMap a b z)‖ *
        ∏ j, ‖spectatorScalingCoefficient a b (w j)‖ := by
  have hv : ‖iteratedFDeriv ℂ n f (spectatorScalingMap a b z)
      (fun j => Pi.single (w j) (1 : ℂ))‖ ≤
      ‖iteratedFDeriv ℂ n f (spectatorScalingMap a b z)‖ := by
    simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℂ n f (spectatorScalingMap a b z)).le_opNorm
        (fun j => Pi.single (w j) (1 : ℂ))
  calc
    _ = (∏ j, ‖spectatorScalingCoefficient a b (w j)‖) *
        ‖iteratedFDeriv ℂ n f (spectatorScalingMap a b z)
          (fun j => Pi.single (w j) (1 : ℂ))‖ := by
      rw [spectatorScaling_iteratedFDeriv_word a b f z n w hf, norm_mul, norm_prod]
    _ ≤ (∏ j, ‖spectatorScalingCoefficient a b (w j)‖) *
        ‖iteratedFDeriv ℂ n f (spectatorScalingMap a b z)‖ :=
      mul_le_mul_of_nonneg_left hv (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := mul_comm _ _

end TheoremT.Continuum
