import TwoElectronSingletRange_v1

/-! The normalized physical singlet and the exact joint fermionic outer-product formula. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem twoElectronRawSinglet_inner (f : SpatialL2 1) (ψ : SpinSpace 2) :
    inner ℂ (twoElectronRawSinglet f) ψ =
      inner ℂ (twoElectronTensor f f) (ψ twoSpin01) -
        inner ℂ (twoElectronTensor f f) (ψ twoSpin10) := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  rw [PiLp.inner_apply,twoSpin_univ]
  simp [twoElectronRawSinglet_apply,h01,h02,h03,h12,h13,h23,
    Ne.symm h12,Ne.symm h13,Ne.symm h23,sub_eq_add_neg]

def twoElectronSinglet (f : SpatialL2 1) : SpinSpace 2 :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • twoElectronRawSinglet f

theorem twoElectronSinglet_fermionic (f : SpatialL2 1) :
    twoElectronSinglet f ∈ fermionicSubspace 2 :=
  (fermionicSubspace 2).smul_mem _ (twoElectronRawSinglet_fermionic f)

theorem twoElectronSinglet_norm_sq (f : SpatialL2 1) (hf : ‖f‖=1) :
    ‖twoElectronSinglet f‖ ^ 2 = 1 := by
  rw [twoElectronSinglet,norm_smul,mul_pow,norm_inv,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg 2),inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),twoElectronRawSinglet_norm_sq,hf]
  norm_num

theorem twoElectronSinglet_norm (f : SpatialL2 1) (hf : ‖f‖=1) :
    ‖twoElectronSinglet f‖ = 1 := by
  have h := twoElectronSinglet_norm_sq f hf
  nlinarith [norm_nonneg (twoElectronSinglet f)]

theorem twoElectron_jointProjection_singlet (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ) =
      inner ℂ (twoElectronSinglet f) ψ • twoElectronSinglet f := by
  rw [twoElectron_jointProjection_rawSinglet f hψ,twoElectronSinglet,
    inner_smul_left,twoElectronRawSinglet_inner,twoElectron_jointAmplitude_offdiagonal f hψ,
    smul_smul]
  congr 1
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hz : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  simp only [map_inv₀,map_div₀,map_one,Complex.conj_ofReal]
  field_simp
  linear_combination inner ℂ (twoElectronTensor f f) (ψ twoSpin01) * hs

theorem twoElectron_fermionic_joint_norm_sq (f : SpatialL2 1) (hf : ‖f‖=1)
    {ψ : SpinSpace 2} (hψ : ψ ∈ fermionicSubspace 2) :
    ‖twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ)‖ ^ 2 =
      ‖inner ℂ (twoElectronSinglet f) ψ‖ ^ 2 := by
  rw [twoElectron_jointProjection_singlet f hψ,norm_smul,twoElectronSinglet_norm f hf,mul_one]

theorem twoElectron_fermionic_projection_norm_sum (f : SpatialL2 1) (hf : ‖f‖=1)
    {ψ : SpinSpace 2} (hψ : ψ ∈ fermionicSubspace 2) :
    ‖twoElectronSpinProjectFirst f ψ‖ ^ 2 + ‖twoElectronSpinProjectSecond f ψ‖ ^ 2 ≤
      ‖ψ‖ ^ 2 + ‖inner ℂ (twoElectronSinglet f) ψ‖ ^ 2 := by
  have h := OperatorTheory.commuting_projections_norm_square
    (twoElectronSpinProjectFirst f).toLinearMap (twoElectronSpinProjectSecond f).toLinearMap
    (twoElectronSpinProjectFirst_isSymmetricProjection f hf)
    (twoElectronSpinProjectSecond_isSymmetricProjection f hf)
    (twoElectronSpinProject_commute f f) ψ
  change ‖twoElectronSpinProjectFirst f ψ‖ ^ 2 + ‖twoElectronSpinProjectSecond f ψ‖ ^ 2 ≤
    ‖ψ‖ ^ 2 + ‖twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ)‖ ^ 2 at h
  rwa [twoElectron_fermionic_joint_norm_sq f hf hψ] at h

#print axioms twoElectronSinglet_norm
#print axioms twoElectronSinglet_fermionic
#print axioms twoElectron_jointProjection_singlet
#print axioms twoElectron_fermionic_joint_norm_sq
#print axioms twoElectron_fermionic_projection_norm_sum
end TheoremT.Continuum
