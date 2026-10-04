import KSMapGeometry_v1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Literal algebra behind circle-invariant KS descent. These identities use
the same four-to-three real KS map as the weak Coulomb chart equations.
They give the four balanced quadratic generators, their radial relation,
and the exact circle invariance of any actual KS pullback. No invariant
polynomial decomposition or convergence theorem is assumed or concluded. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def ksSpinor (y : KSSpace) : Fin 2 → ℂ :=
  ![(y 0 : ℂ)+(y 1 : ℂ)*Complex.I, (y 2 : ℂ)+(y 3 : ℂ)*Complex.I]

def ksDescentQuadratic (X : Fin 3 → ℂ) (r : ℂ) : Fin 2 → Fin 2 → ℂ :=
  ![![(r+X 2)/2, (X 0+Complex.I*X 1)/2],
    ![(X 0-Complex.I*X 1)/2, (r-X 2)/2]]

theorem ksSpinor_balanced_quadratic (y : KSSpace) (i j : Fin 2) :
    ksSpinor y i * star (ksSpinor y j) =
      ksDescentQuadratic (fun k => (ksMap y k : ℂ)) (‖y‖^2 : ℝ) i j := by
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [ksSpinor,ksDescentQuadratic,ksMap,EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ] <;>
    (try simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im]) <;> ring

theorem ksDescentQuadratic_determinant (X : Fin 3 → ℂ) (r : ℂ) :
    ksDescentQuadratic X r 0 0 * ksDescentQuadratic X r 1 1 -
      ksDescentQuadratic X r 0 1 * ksDescentQuadratic X r 1 0 =
        (r^2 - (X 0^2+X 1^2+X 2^2))/4 := by
  simp only [ksDescentQuadratic,Matrix.cons_val_zero,Matrix.cons_val_one]
  calc
    _ = (r^2-X 2^2-X 0^2+Complex.I^2*X 1^2)/4 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem ksMap_radial_relation (y : KSSpace) :
    (‖y‖^2)^2 = (ksMap y 0)^2+(ksMap y 1)^2+(ksMap y 2)^2 := by
  rw [← ksMap_norm_sq,EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ]
  ring

def ksCircleAction (a b : ℝ) (y : KSSpace) : KSSpace := WithLp.toLp 2
  ![a*y 0-b*y 1,b*y 0+a*y 1,a*y 2-b*y 3,b*y 2+a*y 3]

theorem ksMap_circle_action (a b : ℝ) (y : KSSpace) :
    ksMap (ksCircleAction a b y) = (a^2+b^2) • ksMap y := by
  ext i
  fin_cases i <;> simp [ksMap,ksCircleAction] <;> ring

theorem ksMap_circle_invariant {a b : ℝ} (h : a^2+b^2=1) (y : KSSpace) :
    ksMap (ksCircleAction a b y) = ksMap y := by
  rw [ksMap_circle_action,h,one_smul]

theorem ksMap_rotation_invariant (θ : ℝ) (y : KSSpace) :
    ksMap (ksCircleAction (Real.cos θ) (Real.sin θ) y) = ksMap y := by
  apply ksMap_circle_invariant
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem ksSpinor_circle_action (a b : ℝ) (y : KSSpace) (i : Fin 2) :
    ksSpinor (ksCircleAction a b y) i =
      ((a : ℂ)+(b : ℂ)*Complex.I)*ksSpinor y i := by
  fin_cases i <;> apply Complex.ext <;> simp [ksSpinor,ksCircleAction] <;> ring

theorem ks_pullback_circle_invariant {S : Type*} (Ψ : Position × S → ℂ)
    {a b : ℝ} (h : a^2+b^2=1) (y : KSSpace) (s : S) :
    Ψ (ksMap (ksCircleAction a b y),s) = Ψ (ksMap y,s) := by
  rw [ksMap_circle_invariant h]

end TheoremT.Continuum
