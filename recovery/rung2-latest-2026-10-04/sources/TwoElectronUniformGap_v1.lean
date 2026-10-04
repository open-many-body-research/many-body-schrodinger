import TwoElectronPhysicalGroundBranch_v1

/-! Explicit uniform separation for the physical two-electron ground branch
at all real charges Z >= 2. Bounds are deliberately rational and conservative. -/
noncomputable section
namespace TheoremT.Continuum

theorem hydrogenProductRepulsion_le_five_sevenths (Z : ℝ) (hZ : 0 < Z) :
    hydrogenProductRepulsion Z hZ ≤ 5*Z/7 := by
  apply (sq_le_sq₀ (hydrogenProductRepulsion_nonneg Z hZ) (by positivity)).mp
  have h := hydrogenProductRepulsion_sq_le Z hZ
  nlinarith [sq_nonneg Z]

theorem twoElectron_ground_energy_upper (Z : ℝ) (hZ : 0 < Z) :
    (variationalGroundEnergy 2 Z).toReal ≤ -Z^2 + 5*Z/7 := by
  have h := (variational_energy_isGreatest_operatorLowerBounds 2 Z).1
    (hydrogenProductTrial Z Z hZ)
  rw [hydrogenProductTrial_norm,one_pow,mul_one] at h
  change (variationalGroundEnergy 2 Z).toReal ≤
    (inner ℂ (hydrogenProductTrial Z Z hZ : FermionicSpace 2)
      (coulombPartialOperator 2 Z (hydrogenProductTrial Z Z hZ))).re at h
  rw [hydrogenProductTrial_energy] at h
  linarith [hydrogenProductRepulsion_le_five_sevenths Z hZ]

theorem twoElectron_ground_energy_uniform_upper (Z : ℝ) (hZ : 2 ≤ Z) :
    (variationalGroundEnergy 2 Z).toReal ≤ -(9*Z^2/14) := by
  have hp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have h := twoElectron_ground_energy_upper Z hp
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hZ)]

theorem twoElectron_ground_separator_gap (Z : ℝ) (hZ : 2 ≤ Z) :
    Z^2/56 ≤ -(5*Z^2/8) - (variationalGroundEnergy 2 Z).toReal := by
  have h := twoElectron_ground_energy_uniform_upper Z hZ
  linarith

theorem twoElectron_ground_uniform_spectral_gap (Z : ℝ) (hZ : 2 ≤ Z)
    {z : ℂ} (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 Z))
    (hne : z ≠ ((variationalGroundEnergy 2 Z).toReal : ℂ)) :
    Z^2/56 ≤ z.re - (variationalGroundEnergy 2 Z).toReal := by
  have hp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hs : 32 < 9*Z^2 := by nlinarith
  obtain ⟨_,g,_,_,_,hrest⟩ := twoElectron_physical_ground_branch Z hp hs
  have hb := (hrest z hz).resolve_left hne
  linarith [twoElectron_ground_separator_gap Z hZ]

theorem helium_ground_uniform_spectral_gap
    {z : ℂ} (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 2 2))
    (hne : z ≠ ((variationalGroundEnergy 2 2).toReal : ℂ)) :
    (1/14 : ℝ) ≤ z.re - (variationalGroundEnergy 2 2).toReal := by
  convert twoElectron_ground_uniform_spectral_gap 2 (by norm_num) hz hne using 1 <;> norm_num

#print axioms twoElectron_ground_uniform_spectral_gap
#print axioms helium_ground_uniform_spectral_gap
end TheoremT.Continuum
