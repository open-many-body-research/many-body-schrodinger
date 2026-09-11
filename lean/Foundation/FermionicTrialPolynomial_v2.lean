import PotentialPermutation_v2
import ScaledCutoff_v2
import Mathlib.LinearAlgebra.Vandermonde

/-! Concrete nonzero compact smooth alternating trial amplitudes.
The cutoff is symmetrized by a finite product; no radial property of a
noncomputably selected abstract bump function is assumed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace TheoremT.Continuum

def vandermondeAmplitude (N : ℕ) (x : Configuration N) : ℂ :=
  (Matrix.vandermonde (fun i : Fin N => (x (i, 0) : ℂ))).det

theorem vandermondeAmplitude_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (vandermondeAmplitude N) := by
  unfold vandermondeAmplitude
  simp only [Matrix.det_apply, Matrix.vandermonde_apply, Units.smul_def, zsmul_eq_mul]
  apply ContDiff.sum
  intro π _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  exact (Complex.ofRealCLM.contDiff.comp
    (EuclideanSpace.proj (π i, (0 : Fin 3)) : Configuration N →L[ℝ] ℝ).contDiff).pow _

theorem vandermondeAmplitude_permute {N : ℕ} (π : Equiv.Perm (Fin N))
    (x : Configuration N) :
    vandermondeAmplitude N (permuteSpace π x) = permutationSign π * vandermondeAmplitude N x := by
  have hm : Matrix.vandermonde (fun i : Fin N => ((permuteSpace π x) (i, 0) : ℂ)) =
      (Matrix.vandermonde (fun i : Fin N => (x (i, 0) : ℂ))).submatrix π id := by
    ext i j
    rfl
  unfold vandermondeAmplitude
  rw [hm, Matrix.det_permute]
  rfl

def lineConfiguration (N : ℕ) : Configuration N := WithLp.toLp 2 (fun q => (q.1.val : ℝ))

theorem vandermondeAmplitude_line_ne_zero (N : ℕ) :
    vandermondeAmplitude N (lineConfiguration N) ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  apply Fin.ext
  change (((i.val : ℝ) : ℂ)) = (((j.val : ℝ) : ℂ)) at hij
  exact_mod_cast hij

def permutationCutoff (N : ℕ) (R : ℝ) (x : Configuration N) : ℝ :=
  ∏ π : Equiv.Perm (Fin N), scaledCutoff N R (permuteSpace π x)

theorem permutationCutoff_contDiff (N : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (permutationCutoff N R) := by
  apply contDiff_prod
  intro π _
  exact (scaledCutoff_contDiff N R).comp (permuteSpace π).toContinuousLinearEquiv.contDiff

theorem permutationCutoff_invariant {N : ℕ} (R : ℝ)
    (τ : Equiv.Perm (Fin N)) (x : Configuration N) :
    permutationCutoff N R (permuteSpace τ x) = permutationCutoff N R x := by
  change (∏ π : Equiv.Perm (Fin N), scaledCutoff N R (permuteSpace (τ * π) x)) = _
  exact Equiv.prod_comp (Equiv.mulLeft τ)
    (fun π : Equiv.Perm (Fin N) => scaledCutoff N R (permuteSpace π x))

theorem permutationCutoff_compact {N : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (permutationCutoff N R) := by
  apply HasCompactSupport.of_support_subset_isCompact (scaledCutoff_hasCompactSupport (N := N) hR).isCompact
  intro x hx
  apply subset_tsupport
  have hx' : (∏ π : Equiv.Perm (Fin N), scaledCutoff N R (permuteSpace π x)) ≠ 0 := hx
  have h := Finset.prod_ne_zero_iff.mp hx' 1 (Finset.mem_univ _)
  have hone : permuteSpace (1 : Equiv.Perm (Fin N)) x = x := by
    apply (WithLp.ext_iff 2).mpr
    funext q
    rfl
  simpa only [hone, Function.mem_support] using h

theorem permutationCutoff_eq_one {N : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Configuration N} (hx : ‖x‖ ≤ R) : permutationCutoff N R x = 1 := by
  apply Finset.prod_eq_one
  intro π _
  apply scaledCutoff_eq_one hR
  simpa only [(permuteSpace π).norm_map] using hx

def compactAlternatingAmplitude (N : ℕ) (R : ℝ) (x : Configuration N) : ℂ :=
  vandermondeAmplitude N x * (permutationCutoff N R x : ℂ)

theorem compactAlternatingAmplitude_contDiff (N : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (compactAlternatingAmplitude N R) :=
  (vandermondeAmplitude_contDiff N).mul
    (Complex.ofRealCLM.contDiff.comp (permutationCutoff_contDiff N R))

theorem compactAlternatingAmplitude_compact {N : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (compactAlternatingAmplitude N R) := by
  apply HasCompactSupport.of_support_subset_isCompact (permutationCutoff_compact (N := N) hR).isCompact
  intro x hx
  apply subset_tsupport
  change permutationCutoff N R x ≠ 0
  intro hc
  apply hx
  simp [compactAlternatingAmplitude, hc]

theorem compactAlternatingAmplitude_permute {N : ℕ} (R : ℝ)
    (π : Equiv.Perm (Fin N)) (x : Configuration N) :
    compactAlternatingAmplitude N R (permuteSpace π x) =
      permutationSign π * compactAlternatingAmplitude N R x := by
  simp only [compactAlternatingAmplitude, vandermondeAmplitude_permute,
    permutationCutoff_invariant, mul_assoc]

theorem compactAlternatingAmplitude_nonzero (N : ℕ) :
    compactAlternatingAmplitude N (‖lineConfiguration N‖ + 1) (lineConfiguration N) ≠ 0 := by
  have hR : 0 < ‖lineConfiguration N‖ + 1 := by positivity
  rw [compactAlternatingAmplitude, permutationCutoff_eq_one hR (by linarith),
    Complex.ofReal_one, mul_one]
  exact vandermondeAmplitude_line_ne_zero N

#print axioms vandermondeAmplitude_contDiff
#print axioms vandermondeAmplitude_permute
#print axioms vandermondeAmplitude_line_ne_zero
#print axioms permutationCutoff_contDiff
#print axioms permutationCutoff_invariant
#print axioms permutationCutoff_compact
#print axioms permutationCutoff_eq_one
#print axioms compactAlternatingAmplitude_contDiff
#print axioms compactAlternatingAmplitude_compact
#print axioms compactAlternatingAmplitude_permute
#print axioms compactAlternatingAmplitude_nonzero

end TheoremT.Continuum
