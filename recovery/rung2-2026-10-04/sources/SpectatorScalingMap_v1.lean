import HomogeneousSpectatorRescaling_v1
import HomogeneousSpectatorSumAnalytic_v1
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-! Actual independent coordinate-block scaling and its exact interaction
with the polynomial/spectator sum. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {d : ℕ}

def spectatorScalingMap (a b : ℝ) (z : Fin 3 ⊕ Fin d → ℂ) : Fin 3 ⊕ Fin d → ℂ :=
  Sum.elim (fun i => (a : ℂ)*z (.inl i)) (fun i => (b : ℂ)*z (.inr i))

theorem spectatorScalingMap_analyticAt (a b : ℝ) (z : Fin 3 ⊕ Fin d → ℂ) :
    AnalyticAt ℂ (spectatorScalingMap a b) z := by
  apply AnalyticAt.pi
  intro i
  cases i with
  | inl i =>
      exact analyticAt_const.mul
        ((ContinuousLinearMap.proj (Sum.inl i) : (Fin 3 ⊕ Fin d → ℂ) →L[ℂ] ℂ).analyticAt z)
  | inr i =>
      exact analyticAt_const.mul
        ((ContinuousLinearMap.proj (Sum.inr i) : (Fin 3 ⊕ Fin d → ℂ) →L[ℂ] ℂ).analyticAt z)

theorem spectatorScalingMap_inverse_cancel {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (z : Fin 3 ⊕ Fin d → ℂ) :
    spectatorScalingMap a b (spectatorScalingMap a⁻¹ b⁻¹ z) = z := by
  funext i
  cases i <;> simp [spectatorScalingMap,← mul_assoc,ha,hb]

theorem spectatorScalingMap_inverse_norm_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : Fin 3 ⊕ Fin d → ℂ)
    (hza : ∀ i : Fin 3, ‖z (.inl i)‖ ≤ a)
    (hzb : ∀ i : Fin d, ‖z (.inr i)‖ ≤ b) :
    ‖spectatorScalingMap a⁻¹ b⁻¹ z‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  cases i with
  | inl i =>
    simp only [spectatorScalingMap,Sum.elim_inl,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_inv,abs_of_pos ha]
    have hd : ‖z (.inl i)‖/a ≤ 1 := (div_le_iff₀ ha).mpr (by simpa using hza i)
    simpa [div_eq_mul_inv,mul_comm] using hd
  | inr i =>
    simp only [spectatorScalingMap,Sum.elim_inr,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_inv,abs_of_pos hb]
    have hd : ‖z (.inr i)‖/b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hzb i)
    simpa [div_eq_mul_inv,mul_comm] using hd

theorem homogeneousSpectatorSum_rescaling
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) (a b : ℝ)
    (z : Fin 3 ⊕ Fin d → ℂ) :
    homogeneousSpectatorSum (rescaledHomogeneousSpectatorFamily A a b) z =
      homogeneousSpectatorSum A (spectatorScalingMap a b z) := by
  unfold homogeneousSpectatorSum
  apply tsum_congr
  intro k
  exact rescaledHomogeneousSpectatorFamily_eval A hA a b k.1 k.2
    (fun i => z (.inl i)) (fun i => z (.inr i))

end TheoremT.Continuum
