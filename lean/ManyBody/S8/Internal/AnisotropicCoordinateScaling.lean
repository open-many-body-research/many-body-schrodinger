import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Tactic
/-! Separate coordinate-block scaling as an actual continuous linear equivalence.
Its bounds retain the radial and spectator rates individually, with their
ordinary finite Pi coordinate norm. -/
noncomputable section
open scoped BigOperators
namespace ManyBody.S8.MixedAnalytic

def blockScalingCLM (D S : ℝ) : (Fin 3 ⊕ Fin 3 → ℂ) →L[ℂ] (Fin 3 ⊕ Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (Sum.elim (fun _ : Fin 3 => (D : ℂ)) (fun _ : Fin 3 => (S : ℂ)) i) •
      ContinuousLinearMap.proj i

@[simp] theorem blockScalingCLM_inl (D S : ℝ) (z : Fin 3 ⊕ Fin 3 → ℂ) (i : Fin 3) :
    blockScalingCLM D S z (.inl i) = (D : ℂ)*z (.inl i) := rfl
@[simp] theorem blockScalingCLM_inr (D S : ℝ) (z : Fin 3 ⊕ Fin 3 → ℂ) (i : Fin 3) :
    blockScalingCLM D S z (.inr i) = (S : ℂ)*z (.inr i) := rfl

def blockScalingEquiv (D S : ℝ) (hD : 0 < D) (hS : 0 < S) :
    (Fin 3 ⊕ Fin 3 → ℂ) ≃L[ℂ] (Fin 3 ⊕ Fin 3 → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (blockScalingCLM D S) (blockScalingCLM D⁻¹ S⁻¹)
    (by
      intro z
      ext i
      cases i <;> simp [ne_of_gt hD, ne_of_gt hS])
    (by
      intro z
      ext i
      cases i <;> simp [ne_of_gt hD, ne_of_gt hS])

theorem blockScalingEquiv_apply (D S : ℝ) (hD : 0 < D) (hS : 0 < S)
    (z : Fin 3 ⊕ Fin 3 → ℂ) :
    blockScalingEquiv D S hD hS z = blockScalingCLM D S z := rfl

def blockDirectionWeight (D S : ℝ) (z : Fin 3 ⊕ Fin 3 → ℂ) : ℝ :=
  max (D*‖fun i : Fin 3 => z (.inl i)‖) (S*‖fun i : Fin 3 => z (.inr i)‖)

theorem blockScalingCLM_norm_le (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (z : Fin 3 ⊕ Fin 3 → ℂ) :
    ‖blockScalingCLM D S z‖ ≤ blockDirectionWeight D S z := by
  apply (pi_norm_le_iff_of_nonneg
    ((mul_nonneg hD (norm_nonneg _)).trans (le_max_left _ _))).mpr
  intro i
  cases i with
  | inl i =>
    simp only [blockScalingCLM_inl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hD]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i : Fin 3 => z (.inl i)) i)
      hD).trans (le_max_left _ _)
  | inr i =>
    simp only [blockScalingCLM_inr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hS]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i : Fin 3 => z (.inr i)) i)
      hS).trans (le_max_right _ _)

theorem blockScalingCLM_norm_quarter (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (z : Fin 3 ⊕ Fin 3 → ℂ)
    (hX : D*‖fun i : Fin 3 => z (.inl i)‖ ≤ 1/4)
    (hT : S*‖fun i : Fin 3 => z (.inr i)‖ ≤ 1/4) :
    ‖blockScalingCLM D S z‖ ≤ 1/4 :=
  (blockScalingCLM_norm_le D S hD hS z).trans (max_le hX hT)

#print axioms blockScalingEquiv
#print axioms blockScalingCLM_norm_le

theorem blockDirectionWeight_single_left (D S : ℝ) (hD : 0 ≤ D)
    (j : Fin 3) :
    blockDirectionWeight D S (Pi.single (.inl j) (1:ℂ)) = D := by
  have hleft : (fun i : Fin 3 => (Pi.single (Sum.inl j) (1:ℂ) : Fin 3 ⊕ Fin 3 → ℂ) (Sum.inl i)) =
      (Pi.single j (1:ℂ) : Fin 3 → ℂ) := by
    ext i
    simp [Pi.single_apply]
  have hright : (fun i : Fin 3 => (Pi.single (Sum.inl j) (1:ℂ) : Fin 3 ⊕ Fin 3 → ℂ) (Sum.inr i)) = 0 := by
    ext i
    simp
  simp only [blockDirectionWeight, hleft, hright, Pi.norm_single, norm_one,
    norm_zero, mul_one, mul_zero, max_eq_left hD]

theorem blockDirectionWeight_single_right (D S : ℝ) (hS : 0 ≤ S)
    (j : Fin 3) :
    blockDirectionWeight D S (Pi.single (.inr j) (1:ℂ)) = S := by
  have hleft : (fun i : Fin 3 => (Pi.single (Sum.inr j) (1:ℂ) : Fin 3 ⊕ Fin 3 → ℂ) (Sum.inl i)) = 0 := by
    ext i
    simp
  have hright : (fun i : Fin 3 => (Pi.single (Sum.inr j) (1:ℂ) : Fin 3 ⊕ Fin 3 → ℂ) (Sum.inr i)) =
      (Pi.single j (1:ℂ) : Fin 3 → ℂ) := by
    ext i
    simp [Pi.single_apply]
  simp only [blockDirectionWeight, hleft, hright, Pi.norm_single, norm_one,
    norm_zero, mul_one, mul_zero, max_eq_right hS]

theorem blockDirectionWeight_single (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (j : Fin 3 ⊕ Fin 3) :
    blockDirectionWeight D S (Pi.single j (1:ℂ)) =
      Sum.elim (fun _ : Fin 3 => D) (fun _ : Fin 3 => S) j := by
  cases j with
  | inl j => exact blockDirectionWeight_single_left D S hD j
  | inr j => exact blockDirectionWeight_single_right D S hS j

#print axioms blockDirectionWeight_single

end ManyBody.S8.MixedAnalytic
