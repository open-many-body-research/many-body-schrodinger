import ManyBody.S8.Internal.AmbientRealSliceUniqueness
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic
/-! Exact real distance-variable derivative transport.

The coordinatewise real-to-complex cast is the actual proved isometry for the
three-distance Pi max norm.  Genuine analytic formal power series, scalar
restriction and composition with that literal CLM give equality on every
ordered real direction family.  The true real multilinear operator norm is
bounded by the complex one, and every actual ordered coordinate-word derivative
is transported exactly.  This is a distance-space statement, with no electron
Cartesian or Euclidean norm identification.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace ManyBody.S8

theorem ambient_real_iteratedFDeriv_complex_restriction
    {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p))
    (n : ℕ) (v : Fin n → (Fin 3 → ℝ)) :
    iteratedFDeriv ℝ n (f ∘ ambientRealCast) p v =
      iteratedFDeriv ℂ n f (ambientRealCast p) (fun j => ambientRealCast (v j)) := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨R,hR⟩ := hP
  have hreal := (hR.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
    (u := ambientRealCast)
  rw [hreal.iteratedFDeriv_eq_sum_of_completeSpace v,
    hR.iteratedFDeriv_eq_sum_of_completeSpace (fun j => ambientRealCast (v j))]
  apply Finset.sum_congr rfl
  intro σ hσ
  rfl

theorem ambient_real_iteratedFDeriv_norm_le_complex
    {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ ambientRealCast) p‖ ≤
      ‖iteratedFDeriv ℂ n f (ambientRealCast p)‖ := by
  apply (iteratedFDeriv ℝ n (f ∘ ambientRealCast) p).opNorm_le_bound
    (norm_nonneg _)
  intro v
  rw [ambient_real_iteratedFDeriv_complex_restriction hf n v]
  simpa only [ambientRealCast_norm] using
    (iteratedFDeriv ℂ n f (ambientRealCast p)).le_opNorm
      (fun j => ambientRealCast (v j))

theorem ambientRealCast_coordinate_direction (j : Fin 3) :
    ambientRealCast (Pi.single j (1 : ℝ))=Pi.single j (1 : ℂ) := by
  ext k
  by_cases hk : k=j
  · subst k
    simp [ambientRealCast_apply]
  · simp [ambientRealCast_apply,Pi.single_eq_of_ne hk]

def ambientRealDistanceWordDerivative {n : ℕ}
    (f : (Fin 3 → ℂ) → ℂ) (w : Fin n → Fin 3) (p : Fin 3 → ℝ) : ℂ :=
  iteratedFDeriv ℝ n (f ∘ ambientRealCast) p (fun j => Pi.single (w j) (1 : ℝ))

theorem ambient_real_iteratedFDeriv_coordinate_word
    {f : (Fin 3 → ℂ) → ℂ} {p : Fin 3 → ℝ}
    (hf : AnalyticAt ℂ f (ambientRealCast p)) (n : ℕ) (w : Fin n → Fin 3) :
    ambientRealDistanceWordDerivative f w p =
      iteratedFDeriv ℂ n f (ambientRealCast p) (fun j => Pi.single (w j) (1 : ℂ)) := by
  rw [ambientRealDistanceWordDerivative,
    ambient_real_iteratedFDeriv_complex_restriction hf n]
  congr 1
  funext j
  exact ambientRealCast_coordinate_direction (w j)

theorem ambientRealDistanceWordDerivative_norm_le {n : ℕ}
    (f : (Fin 3 → ℂ) → ℂ) (w : Fin n → Fin 3) (p : Fin 3 → ℝ) :
    ‖ambientRealDistanceWordDerivative f w p‖≤
      ‖iteratedFDeriv ℝ n (f ∘ ambientRealCast) p‖ := by
  have hd (j : Fin n) : ‖(Pi.single (w j) (1 : ℝ) : Fin 3 → ℝ)‖=1 := by
    rw [Pi.norm_single,norm_one]
  simpa only [ambientRealDistanceWordDerivative,hd,Finset.prod_const_one,mul_one] using
    (iteratedFDeriv ℝ n (f ∘ ambientRealCast) p).le_opNorm
      (fun j => Pi.single (w j) (1 : ℝ))

#print axioms ambient_real_iteratedFDeriv_complex_restriction
#print axioms ambient_real_iteratedFDeriv_norm_le_complex
#print axioms ambient_real_iteratedFDeriv_coordinate_word
#print axioms ambientRealDistanceWordDerivative_norm_le
end ManyBody.S8
