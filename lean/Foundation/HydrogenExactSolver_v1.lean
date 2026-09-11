import HydrogenSpinGround_v1
import CoulombUnboundNonpositive_v1

/-! A computable exact rational spectral-energy enclosure for one electron and
natural nuclear charge, including zero. Precision is an accepted finite input;
the returned interval has zero width. No general-N algorithm is asserted. -/

namespace TheoremT.Continuum

/-- Exact rational output; this definition is computable and uses no choice. -/
def hydrogenExactSolver (Z _p : ℕ) : ℚ × ℚ :=
  let E : ℚ := -(Z : ℚ)^2 / 2
  (E, E)

/-- Finite exact-certificate checker. It accepts precisely the canonical exact
energy endpoints; soundness is proved against the actual continuum spectrum below. -/
def hydrogenExactCertificateCheck (Z : ℕ) (I : ℚ × ℚ) : Bool :=
  decide (I.1 = -(Z : ℚ)^2 / 2 ∧ I.2 = -(Z : ℚ)^2 / 2)

theorem hydrogenExactSolver_precision_independent (Z p q : ℕ) :
    hydrogenExactSolver Z p = hydrogenExactSolver Z q := rfl

theorem hydrogen_nat_spectral_energy (Z : ℕ) :
    spectralGroundEnergy 1 (Z : ℝ) = (((-(Z : ℚ)^2 / 2 : ℚ) : ℝ) : EReal) := by
  by_cases hZ : Z = 0
  · subst Z
    simp only [Nat.cast_zero, Rat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
      neg_zero, zero_div, EReal.coe_zero]
    rw [spectralGroundEnergy_eq_variationalGroundEnergy,
      variational_ground_energy_eq_zero_of_charge_nonpos 1 (by norm_num : (0 : ℝ) ≤ 0)]
  · have hpos : 0 < (Z : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hZ
    rw [hydrogen_spectral_ground_energy (Z : ℝ) hpos]
    congr 1
    push_cast
    ring

theorem hydrogenExactSolver_correct (Z p : ℕ) :
    (((hydrogenExactSolver Z p).1 : ℝ) : EReal) ≤ spectralGroundEnergy 1 (Z : ℝ) ∧
      spectralGroundEnergy 1 (Z : ℝ) ≤ (((hydrogenExactSolver Z p).2 : ℝ) : EReal) ∧
      (hydrogenExactSolver Z p).2 - (hydrogenExactSolver Z p).1 = 0 ∧
      (hydrogenExactSolver Z p).2 - (hydrogenExactSolver Z p).1 ≤ (1 : ℚ) / 2^p := by
  rw [hydrogen_nat_spectral_energy]
  dsimp [hydrogenExactSolver]
  refine ⟨le_rfl, le_rfl, sub_self _, ?_⟩
  rw [sub_self]
  positivity

theorem hydrogenExactCertificateCheck_accepts (Z p : ℕ) :
    hydrogenExactCertificateCheck Z (hydrogenExactSolver Z p) = true := by
  simp [hydrogenExactCertificateCheck, hydrogenExactSolver]

theorem hydrogenExactCertificateCheck_sound (Z p : ℕ) (I : ℚ × ℚ)
    (hI : hydrogenExactCertificateCheck Z I = true) :
    ((I.1 : ℝ) : EReal) ≤ spectralGroundEnergy 1 (Z : ℝ) ∧
      spectralGroundEnergy 1 (Z : ℝ) ≤ ((I.2 : ℝ) : EReal) ∧
      I.2 - I.1 = 0 ∧ I.2 - I.1 ≤ (1 : ℚ) / 2^p := by
  have he : I.1 = -(Z : ℚ)^2 / 2 ∧ I.2 = -(Z : ℚ)^2 / 2 := by
    simpa only [hydrogenExactCertificateCheck, decide_eq_true_eq] using hI
  have hpair : I = hydrogenExactSolver Z p := Prod.ext he.1 he.2
  rw [hpair]
  exact hydrogenExactSolver_correct Z p

-- These expected sample outputs are proved by kernel-reduced decidable equality.
theorem hydrogenExactSolver_sample_zero : hydrogenExactSolver 0 0 = (0, 0) := by decide +kernel
theorem hydrogenExactSolver_sample_one : hydrogenExactSolver 1 10 = (-1/2, -1/2) := by decide +kernel
theorem hydrogenExactSolver_sample_two : hydrogenExactSolver 2 100 = (-2, -2) := by decide +kernel
theorem hydrogenExactSolver_sample_three : hydrogenExactSolver 3 1000 = (-9/2, -9/2) := by decide +kernel
theorem hydrogenExactSolver_sample_hundred : hydrogenExactSolver 100 1000000 = (-5000, -5000) := by decide +kernel
theorem hydrogenExactCertificateCheck_sample_reject : hydrogenExactCertificateCheck 1 (0, 0) = false := by decide +kernel

-- Evaluator output demonstrates execution; the proof above does not trust it.
#eval ([ (0,0), (1,10), (2,100), (3,1000), (100,1000000) ] : List (ℕ × ℕ)).map
  (fun zp => (zp.1, zp.2, hydrogenExactSolver zp.1 zp.2,
    hydrogenExactCertificateCheck zp.1 (hydrogenExactSolver zp.1 zp.2)))

#print axioms hydrogenExactSolver_sample_zero
#print axioms hydrogenExactSolver_sample_one
#print axioms hydrogenExactSolver_sample_two
#print axioms hydrogenExactSolver_sample_three
#print axioms hydrogenExactSolver_sample_hundred
#print axioms hydrogenExactCertificateCheck_sample_reject
#print axioms hydrogen_nat_spectral_energy
#print axioms hydrogenExactSolver_correct
#print axioms hydrogenExactCertificateCheck_sound
#print axioms hydrogenExactCertificateCheck_accepts
end TheoremT.Continuum
