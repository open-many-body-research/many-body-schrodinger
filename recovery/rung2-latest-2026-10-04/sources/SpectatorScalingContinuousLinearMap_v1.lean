import SpectatorScalingMap_v1
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! The actual independent block scaling as a complex continuous linear
map. Coordinate unit vectors retain their individual block factors;
there is no replacement by the norm of the whole operator. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
variable {d : ℕ}

def spectatorScalingCoefficient (a b : ℝ) : Fin 3 ⊕ Fin d → ℂ :=
  Sum.elim (fun _ => (a : ℂ)) (fun _ => (b : ℂ))

def spectatorScalingContinuousLinearMap (a b : ℝ) :
    (Fin 3 ⊕ Fin d → ℂ) →L[ℂ] (Fin 3 ⊕ Fin d → ℂ) :=
  ContinuousLinearMap.pi (fun i => spectatorScalingCoefficient a b i •
    (ContinuousLinearMap.proj i : (Fin 3 ⊕ Fin d → ℂ) →L[ℂ] ℂ))

theorem spectatorScalingContinuousLinearMap_coe (a b : ℝ) :
    (spectatorScalingContinuousLinearMap a b :
      (Fin 3 ⊕ Fin d → ℂ) → (Fin 3 ⊕ Fin d → ℂ)) = spectatorScalingMap a b := by
  funext z i
  cases i <;> rfl

theorem spectatorScalingContinuousLinearMap_single (a b : ℝ) (i : Fin 3 ⊕ Fin d) :
    spectatorScalingContinuousLinearMap a b (Pi.single i (1 : ℂ)) =
      spectatorScalingCoefficient a b i • Pi.single i (1 : ℂ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [spectatorScalingContinuousLinearMap]
  · simp [spectatorScalingContinuousLinearMap, Pi.single_apply, h]

theorem spectatorScalingContinuousLinearMap_norm_single (a b : ℝ) (i : Fin 3 ⊕ Fin d) :
    ‖spectatorScalingContinuousLinearMap a b (Pi.single i (1 : ℂ))‖ =
      ‖spectatorScalingCoefficient a b i‖ := by
  rw [spectatorScalingContinuousLinearMap_single, norm_smul, Pi.norm_single, norm_one, mul_one]

theorem spectatorScalingContinuousLinearMap_norm_single_inl (a b : ℝ) (i : Fin 3) :
    ‖spectatorScalingContinuousLinearMap (d := d) a b (Pi.single (.inl i) (1 : ℂ))‖ = |a| := by
  rw [spectatorScalingContinuousLinearMap_norm_single]
  simp [spectatorScalingCoefficient, Complex.norm_real, Real.norm_eq_abs]

theorem spectatorScalingContinuousLinearMap_norm_single_inr (a b : ℝ) (i : Fin d) :
    ‖spectatorScalingContinuousLinearMap a b (Pi.single (.inr i) (1 : ℂ))‖ = |b| := by
  rw [spectatorScalingContinuousLinearMap_norm_single]
  simp [spectatorScalingCoefficient, Complex.norm_real, Real.norm_eq_abs]

end TheoremT.Continuum
