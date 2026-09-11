import ScalarSpinFormAssembly_v1
import TwoElectronNormalizedSinglet_v1

/-! The normalized singlet preserves the physical spatial form value. -/
noncomputable section
namespace TheoremT.Continuum

def twoElectronSingletSpinWeight (σ : SpinConfiguration 2) : ℂ :=
  (if σ = twoSpin01 then 1 else 0) - (if σ = twoSpin10 then 1 else 0)

theorem twoElectronRawSinglet_weight (f : SpatialL2 1) (σ : SpinConfiguration 2) :
    twoElectronRawSinglet f σ = twoElectronSingletSpinWeight σ • twoElectronTensor f f := by
  rw [twoElectronRawSinglet_apply]
  unfold twoElectronSingletSpinWeight
  split_ifs <;> simp

theorem twoElectronSingletSpinWeight_norm_sum :
    (∑ σ : SpinConfiguration 2, ‖twoElectronSingletSpinWeight σ‖^2) = 2 := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  rw [twoSpin_univ]
  simp [twoElectronSingletSpinWeight,h01,h02,h03,h12,h13,h23,
    Ne.symm h12,Ne.symm h13,Ne.symm h23]
  norm_num

theorem twoElectronRawSinglet_formValue (Z : ℝ) (f : SpatialL2 1) {q : ℝ}
    (hq : scalarCoulombH1FormValue 2 Z (twoElectronTensor f f) q) :
    coulombH1FormValue 2 Z (twoElectronRawSinglet f) (2*q) := by
  have h := coulombH1FormValue_of_scalar_components (Z := Z) (twoElectronRawSinglet f)
    (twoElectronRawSinglet_fermionic f) (fun σ => ‖twoElectronSingletSpinWeight σ‖^2 * q) (fun σ => ?_)
  · simpa only [← Finset.sum_mul,twoElectronSingletSpinWeight_norm_sum] using h
  · rw [twoElectronRawSinglet_weight]
    exact scalarCoulombH1FormValue_smul _ hq

theorem twoElectronSinglet_formValue (Z : ℝ) (f : SpatialL2 1) {q : ℝ}
    (hq : scalarCoulombH1FormValue 2 Z (twoElectronTensor f f) q) :
    coulombH1FormValue 2 Z (twoElectronSinglet f) q := by
  have h := coulombH1FormValue_smul (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
    (twoElectronRawSinglet_formValue Z f hq)
  have he : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖^2 * (2*q) = q := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr (by norm_num)),inv_pow,Real.sq_sqrt (by norm_num)]
    ring
  rwa [he] at h

#print axioms twoElectronRawSinglet_weight
#print axioms twoElectronSingletSpinWeight_norm_sum
#print axioms twoElectronRawSinglet_formValue
#print axioms twoElectronSinglet_formValue
end TheoremT.Continuum
