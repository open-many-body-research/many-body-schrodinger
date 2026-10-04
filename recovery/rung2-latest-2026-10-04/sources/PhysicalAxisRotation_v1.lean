import ConfigurationRotation_v1
import Mathlib.Analysis.Complex.Trigonometric

/-! The actual rotation of Euclidean physical space around the third axis.
The transverse convention is (x,y) -> (cos(theta)x-sin(theta)y,
sin(theta)x+cos(theta)y), consistent with v=x+I*y. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def physicalAxisRotationLinear (θ : ℝ) : Position →ₗ[ℝ] Position where
  toFun X := WithLp.toLp 2
    ![Real.cos θ*X 0-Real.sin θ*X 1, Real.sin θ*X 0+Real.cos θ*X 1, X 2]
  map_add' X Y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c X := by
    ext i
    fin_cases i <;> simp <;> ring

theorem physicalAxisRotationLinear_norm (θ : ℝ) (X : Position) :
    ‖physicalAxisRotationLinear θ X‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,physicalAxisRotationLinear]
  linear_combination ((X 0)^2+(X 1)^2)*(Real.cos_sq_add_sin_sq θ)

theorem physicalAxisRotationLinear_neg_apply (θ : ℝ) (X : Position) :
    physicalAxisRotationLinear (-θ) (physicalAxisRotationLinear θ X) = X := by
  ext i
  fin_cases i
  · simp [physicalAxisRotationLinear,Real.cos_neg,Real.sin_neg]
    linear_combination (X 0)*(Real.cos_sq_add_sin_sq θ)
  · simp [physicalAxisRotationLinear,Real.cos_neg,Real.sin_neg]
    linear_combination (X 1)*(Real.cos_sq_add_sin_sq θ)
  · simp [physicalAxisRotationLinear]

def physicalAxisRotation (θ : ℝ) : Position ≃ₗᵢ[ℝ] Position where
  toLinearEquiv :=
    { physicalAxisRotationLinear θ with
      invFun := physicalAxisRotationLinear (-θ)
      left_inv := physicalAxisRotationLinear_neg_apply θ
      right_inv := by
        intro X
        change physicalAxisRotationLinear θ (physicalAxisRotationLinear (-θ) X) = X
        simpa only [neg_neg] using physicalAxisRotationLinear_neg_apply (-θ) X }
  norm_map' := physicalAxisRotationLinear_norm θ

theorem physicalAxisRotation_apply (θ : ℝ) (X : Position) :
    physicalAxisRotation θ X = WithLp.toLp 2
      ![Real.cos θ*X 0-Real.sin θ*X 1, Real.sin θ*X 0+Real.cos θ*X 1, X 2] := rfl

theorem physicalAxisRotation_apply_zero (θ : ℝ) (X : Position) :
    physicalAxisRotation θ X 0 = Real.cos θ*X 0-Real.sin θ*X 1 := rfl

theorem physicalAxisRotation_apply_one (θ : ℝ) (X : Position) :
    physicalAxisRotation θ X 1 = Real.sin θ*X 0+Real.cos θ*X 1 := rfl

theorem physicalAxisRotation_apply_two (θ : ℝ) (X : Position) :
    physicalAxisRotation θ X 2 = X 2 := rfl

theorem physicalAxisRotation_axis (θ s : ℝ) :
    physicalAxisRotation θ (WithLp.toLp 2 ![0,0,s]) = WithLp.toLp 2 ![0,0,s] := by
  ext i
  fin_cases i <;> simp [physicalAxisRotation_apply]

end TheoremT.Continuum
