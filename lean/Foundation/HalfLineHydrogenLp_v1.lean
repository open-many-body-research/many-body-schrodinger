import HalfLineCompactPairing_v1
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.HalfLine

def radialExp (Z r : ℝ) : ℂ := (Real.exp (-Z*r) : ℂ)
def radialGround (Z r : ℝ) : ℂ := (r : ℂ) * radialExp Z r
def radialGroundPrime (Z r : ℝ) : ℂ := radialExp Z r - (Z:ℂ) * radialGround Z r

theorem radialExp_contDiff (Z : ℝ) : ContDiff ℝ ∞ (radialExp Z) := by
  unfold radialExp
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).exp)

theorem radialGround_contDiff (Z : ℝ) : ContDiff ℝ ∞ (radialGround Z) :=
  Complex.ofRealCLM.contDiff.mul (radialExp_contDiff Z)

theorem radialExp_memLp {Z : ℝ} (hZ : 0 < Z) : MemLp (radialExp Z) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (radialExp_contDiff Z).continuous.aestronglyMeasurable).2
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 0) (p := 1) (b := 2*Z) (by norm_num) (by norm_num) (by positivity : 0 < 2*Z)
  have he : (fun r => ‖radialExp Z r‖^2) = (fun r => Real.exp (-(2*Z)*r)) := by
    funext r
    simp only [radialExp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  simpa [μ, IntegrableOn] using hi

theorem radialGround_memLp {Z : ℝ} (hZ : 0 < Z) : MemLp (radialGround Z) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (radialGround_contDiff Z).continuous.aestronglyMeasurable).2
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 2) (p := 1) (b := 2*Z) (by norm_num) (by norm_num) (by positivity : 0 < 2*Z)
  have he : (fun r => ‖radialGround Z r‖^2) = (fun r => r^2*Real.exp (-(2*Z)*r)) := by
    funext r
    simp only [radialGround, radialExp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, sq_abs, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he]
  simpa [μ, IntegrableOn, Real.rpow_two] using hi

theorem radialGroundPrime_memLp {Z : ℝ} (hZ : 0 < Z) :
    MemLp (radialGroundPrime Z) 2 μ :=
  (radialExp_memLp hZ).sub ((radialGround_memLp hZ).const_smul (Z:ℂ))

theorem radialGround_hasDerivAt (Z r : ℝ) :
    HasDerivAt (radialGround Z) (radialGroundPrime Z r) r := by
  have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 r := by
    simpa using! (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
  have hd := ((hasDerivAt_id r).const_mul (-Z)).exp
  have hce := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hd
  convert! hx.mul hce using 1 <;>
    simp [radialGround, radialGroundPrime, radialExp, Complex.real_smul] <;> ring

def radialGroundL2 (Z : ℝ) (hZ : 0 < Z) : E := (radialGround_memLp hZ).toLp (radialGround Z)
def radialGroundPrimeL2 (Z : ℝ) (hZ : 0 < Z) : E :=
  (radialGroundPrime_memLp hZ).toLp (radialGroundPrime Z)

theorem radialGroundL2_coe (Z : ℝ) (hZ : 0 < Z) :
    (radialGroundL2 Z hZ : ℝ → ℂ) =ᵐ[μ] radialGround Z :=
  (radialGround_memLp hZ).coeFn_toLp

theorem radialGroundPrimeL2_coe (Z : ℝ) (hZ : 0 < Z) :
    (radialGroundPrimeL2 Z hZ : ℝ → ℂ) =ᵐ[μ] radialGroundPrime Z :=
  (radialGroundPrime_memLp hZ).coeFn_toLp

#print axioms radialGround_memLp
#print axioms radialGroundPrime_memLp
#print axioms radialGround_hasDerivAt
end TheoremT.HalfLine
