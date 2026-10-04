import PhysicalComplexAxisSlice_v1

/-! The real physical positions corresponding to the literal complex axis
slice. The input norm is the coordinate sup norm; each output Position has
its actual Euclidean norm. Their comparison records the factor sqrt(3). -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def physicalRealAxisSpatial (z : Fin 4 → ℝ) : Position :=
  WithLp.toLp 2 ![z 0,z 1,z 2]

def physicalRealAxisSpectator (z : Fin 4 → ℝ) : Position :=
  WithLp.toLp 2 ![0,0,z 3]

theorem physicalRealAxis_complexification (z : Fin 4 → ℝ) :
    physicalComplexAxisSlice (fun i => (z i : ℂ)) =
      Sum.elim (fun i => (physicalRealAxisSpatial z i : ℂ))
        (fun i => (physicalRealAxisSpectator z i : ℂ)) := by
  funext j
  cases j with
  | inl i => fin_cases i <;> simp [physicalComplexAxisSlice,physicalRealAxisSpatial]
  | inr i => fin_cases i <;> simp [physicalComplexAxisSlice,physicalRealAxisSpectator]

theorem physicalRealAxisSpectator_norm (z : Fin 4 → ℝ) :
    ‖physicalRealAxisSpectator z‖ = ‖z 3‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,physicalRealAxisSpectator]

theorem physicalRealAxisSpatial_norm_sq (z : Fin 4 → ℝ) :
    ‖physicalRealAxisSpatial z‖^2 = (z 0)^2+(z 1)^2+(z 2)^2 := by
  simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,physicalRealAxisSpatial]

theorem physicalRealAxisSpatial_norm_le (z : Fin 4 → ℝ) :
    ‖physicalRealAxisSpatial z‖ ≤ Real.sqrt 3*‖z‖ := by
  have hi (i : Fin 4) : (z i)^2 ≤ ‖z‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (z i)) (norm_nonneg z)).mpr (norm_le_pi_norm z i)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg z))).mp
  rw [physicalRealAxisSpatial_norm_sq,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
  linarith [hi 0,hi 1,hi 2]

theorem physicalRealAxis_domain_of_norm_lt {ρ r : ℝ} {z : Fin 4 → ℝ}
    (hz : ‖z‖ < min (ρ/Real.sqrt 3) r) :
    ‖physicalRealAxisSpatial z‖ < ρ ∧ ‖physicalRealAxisSpectator z‖ < r := by
  obtain ⟨hρ,hr⟩ := lt_min_iff.mp hz
  constructor
  · apply (physicalRealAxisSpatial_norm_le z).trans_lt
    have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    simpa only [mul_comm] using (lt_div_iff₀ hsqrt).mp hρ
  · rw [physicalRealAxisSpectator_norm]
    exact (norm_le_pi_norm z 3).trans_lt hr

end TheoremT.Continuum
