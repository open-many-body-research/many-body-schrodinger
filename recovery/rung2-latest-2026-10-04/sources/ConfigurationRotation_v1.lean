import ContinuumFoundation_v1

/-! Actual simultaneous orthogonal transformations of all electron positions.
This includes reflections and proves exact potential invariance even for the
chosen representative on collision sets. Spin labels are not rotated. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def rotateConfigurationLinear (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position) :
    Configuration N →ₗ[ℝ] Configuration N where
  toFun x := WithLp.toLp 2 (fun k => (R (position x k.1)) k.2)
  map_add' x y := by
    ext ⟨i,k⟩
    change (R (position x i + position y i)) k = (R (position x i)) k + (R (position y i)) k
    rw [map_add]
    rfl
  map_smul' c x := by
    ext ⟨i,k⟩
    change (R (c • position x i)) k = c * (R (position x i)) k
    rw [map_smul]
    rfl

theorem position_rotateConfigurationLinear (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position)
    (x : Configuration N) (i : Fin N) :
    position (rotateConfigurationLinear N R x) i = R (position x i) := by
  ext k
  rfl

theorem configuration_norm_sq_positions {N : ℕ} (x : Configuration N) :
    ‖x‖^2 = ∑ i : Fin N, ‖position x i‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type,position]

def configurationRotation (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position) :
    Configuration N ≃ₗᵢ[ℝ] Configuration N where
  toLinearEquiv :=
    { rotateConfigurationLinear N R with
      invFun := rotateConfigurationLinear N R.symm
      left_inv := by
        intro x
        ext ⟨i,k⟩
        change (R.symm (position (rotateConfigurationLinear N R x) i)) k = x (i,k)
        rw [position_rotateConfigurationLinear,R.symm_apply_apply]
        rfl
      right_inv := by
        intro x
        ext ⟨i,k⟩
        change (R (position (rotateConfigurationLinear N R.symm x) i)) k = x (i,k)
        rw [position_rotateConfigurationLinear,R.apply_symm_apply]
        rfl }
  norm_map' x := by
    change ‖rotateConfigurationLinear N R x‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [configuration_norm_sq_positions,configuration_norm_sq_positions]
    simp only [position_rotateConfigurationLinear,R.norm_map]

theorem position_configurationRotation (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position)
    (x : Configuration N) (i : Fin N) :
    position (configurationRotation N R x) i = R (position x i) :=
  position_rotateConfigurationLinear N R x i

theorem coulombPotential_configurationRotation (N : ℕ) (Z : ℝ)
    (R : Position ≃ₗᵢ[ℝ] Position) (x : Configuration N) :
    coulombPotential N Z (configurationRotation N R x) = coulombPotential N Z x := by
  simp only [coulombPotential,position_configurationRotation,← map_sub,R.norm_map]

theorem configurationRotation_permuteSpace (N : ℕ) (R : Position ≃ₗᵢ[ℝ] Position)
    (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    configurationRotation N R (permuteSpace π x) =
      permuteSpace π (configurationRotation N R x) := by
  ext ⟨i,k⟩
  change (R (position (permuteSpace π x) i)) k = (R (position x (π i))) k
  rfl

#print axioms configurationRotation
#print axioms coulombPotential_configurationRotation
#print axioms configurationRotation_permuteSpace
end TheoremT.Continuum
