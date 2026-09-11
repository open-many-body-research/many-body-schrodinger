import HydrogenExactSolver_v1

/-! Readable semantic audit of the executable exact one-electron enclosure and
checker. Physical spectralGroundEnergy is the unchanged continuum definition. -/
namespace TheoremT.Continuum

theorem audit_hydrogen_exact_solver (Z p : ℕ) :
    (((hydrogenExactSolver Z p).1 : ℝ) : EReal) ≤ spectralGroundEnergy 1 (Z : ℝ) ∧
      spectralGroundEnergy 1 (Z : ℝ) ≤ (((hydrogenExactSolver Z p).2 : ℝ) : EReal) ∧
      (hydrogenExactSolver Z p).2 - (hydrogenExactSolver Z p).1 = 0 ∧
      (hydrogenExactSolver Z p).2 - (hydrogenExactSolver Z p).1 ≤ (1 : ℚ) / 2^p :=
  hydrogenExactSolver_correct Z p

theorem audit_hydrogen_exact_certificate (Z p : ℕ) (I : ℚ × ℚ)
    (hI : hydrogenExactCertificateCheck Z I = true) :
    ((I.1 : ℝ) : EReal) ≤ spectralGroundEnergy 1 (Z : ℝ) ∧
      spectralGroundEnergy 1 (Z : ℝ) ≤ ((I.2 : ℝ) : EReal) ∧
      I.2 - I.1 = 0 ∧ I.2 - I.1 ≤ (1 : ℚ) / 2^p :=
  hydrogenExactCertificateCheck_sound Z p I hI

#print hydrogenExactSolver
#print hydrogenExactCertificateCheck
#print spectralGroundEnergy
#check audit_hydrogen_exact_solver
#check audit_hydrogen_exact_certificate
#check hydrogenExactSolver_precision_independent
#print axioms audit_hydrogen_exact_solver
#print axioms audit_hydrogen_exact_certificate
#print axioms hydrogenExactCertificateCheck_accepts
#print axioms hydrogenExactSolver_sample_zero
#print axioms hydrogenExactSolver_sample_one
#print axioms hydrogenExactSolver_sample_two
#print axioms hydrogenExactSolver_sample_three
#print axioms hydrogenExactSolver_sample_hundred
#print axioms hydrogenExactCertificateCheck_sample_reject
end TheoremT.Continuum
