import TwoElectronCoordinateProduct_v1

/-! Exact orthogonal center/relative coordinates. The second three-vector is
(x0-x1)/sqrt(2); the Lebesgue measure and kinetic metric are preserved. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def twoElectronHadamardLinear : Configuration 2 →ₗ[ℝ] Configuration 2 where
  toFun x := WithLp.toLp 2 (fun k =>
    if k.1 = 0 then (x (0,k.2) + x (1,k.2)) / Real.sqrt 2
      else (x (0,k.2) - x (1,k.2)) / Real.sqrt 2)
  map_add' x y := by
    apply (WithLp.ext_iff 2).mpr
    funext ⟨i,k⟩
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    apply (WithLp.ext_iff 2).mpr
    funext ⟨i,k⟩
    fin_cases i <;> simp <;> ring

theorem twoElectronHadamard_first (x : Configuration 2) (k : Fin 3) :
    twoElectronHadamardLinear x (0,k) = (x (0,k) + x (1,k)) / Real.sqrt 2 := by
  simp [twoElectronHadamardLinear]

theorem twoElectronHadamard_second (x : Configuration 2) (k : Fin 3) :
    twoElectronHadamardLinear x (1,k) = (x (0,k) - x (1,k)) / Real.sqrt 2 := by
  simp [twoElectronHadamardLinear]

theorem twoElectronHadamard_involutive : Function.Involutive twoElectronHadamardLinear := by
  intro x
  apply (WithLp.ext_iff 2).mpr
  funext ⟨i,k⟩
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hz : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  change twoElectronHadamardLinear (twoElectronHadamardLinear x) (i,k) = x (i,k)
  fin_cases i <;> simp [twoElectronHadamardLinear]
  all_goals field_simp [hz]
  all_goals rw [hs]; ring

theorem configuration_two_norm_sq (x : Configuration 2) :
    ‖x‖^2 = ∑ k : Fin 3, ((x (0,k))^2 + (x (1,k))^2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Coordinate,Fintype.sum_prod_type,Fin.sum_univ_two,Finset.sum_add_distrib]

theorem twoElectronHadamard_norm (x : Configuration 2) :
    ‖twoElectronHadamardLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [configuration_two_norm_sq,configuration_two_norm_sq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [twoElectronHadamard_first,twoElectronHadamard_second]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow,div_pow,hs]
  ring

def twoElectronRelativeEquiv : Configuration 2 ≃ₗᵢ[ℝ] Configuration 2 :=
  { twoElectronHadamardLinear with
    invFun := twoElectronHadamardLinear
    left_inv := twoElectronHadamard_involutive
    right_inv := twoElectronHadamard_involutive
    norm_map' := twoElectronHadamard_norm }

theorem twoElectronRelativeEquiv_measurePreserving :
    MeasurePreserving twoElectronRelativeEquiv := twoElectronRelativeEquiv.measurePreserving

theorem twoElectronRelativeEquiv_pair_position (x : Configuration 2) :
    position (twoElectronRelativeEquiv x) 1 =
      (Real.sqrt 2)⁻¹ • (position x 0 - position x 1) := by
  apply (WithLp.ext_iff 2).mpr
  funext k
  change twoElectronHadamardLinear x (1,k) = (Real.sqrt 2)⁻¹ * (x (0,k) - x (1,k))
  rw [twoElectronHadamard_second]
  ring

theorem twoElectronRelativeEquiv_pair_norm (x : Configuration 2) :
    ‖position x 0 - position x 1‖ =
      Real.sqrt 2 * ‖position (twoElectronRelativeEquiv x) 1‖ := by
  rw [twoElectronRelativeEquiv_pair_position,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num)))]
  field_simp

#print axioms twoElectronHadamard_involutive
#print axioms twoElectronHadamard_norm
#print axioms twoElectronRelativeEquiv_measurePreserving
#print axioms twoElectronRelativeEquiv_pair_norm
end TheoremT.Continuum
