import ManyBody.S8.Internal.PhysicalComplexCoordinates
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic
/-! Exact transport of every genuine real physical derivative to the
complex derivative of the literal function on the six coordinate values.

The actual local formal power series is restricted from complex to real
scalars and composed with the proved physical coordinate CLM. The derivative
permutation formula supplies equality on all ordered directions. Its actual
Euclidean-to-Pi contraction gives an operator norm inequality without any
identification of the two norms. Spectator centering uses exact translation.
-/
noncomputable section
open scoped BigOperators
namespace ManyBody.S8
open TheoremT.Continuum

theorem physical_iteratedFDeriv_complex_restriction
    {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesCLM x))
    (n : ℕ) (v : Fin n → Position × Position) :
    iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesCLM) x v =
      iteratedFDeriv ℂ n f (physicalComplexCoordinatesCLM x)
        (fun i => physicalComplexCoordinatesCLM (v i)) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨R,hR⟩ := hp
  have hreal := (hR.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
    (u := physicalComplexCoordinatesCLM)
  rw [hreal.iteratedFDeriv_eq_sum_of_completeSpace v,
    hR.iteratedFDeriv_eq_sum_of_completeSpace (fun i => physicalComplexCoordinatesCLM (v i))]
  apply Finset.sum_congr rfl
  intro σ hσ
  rfl

theorem physical_iteratedFDeriv_norm_le_complex
    {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesCLM x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesCLM) x‖ ≤
      ‖iteratedFDeriv ℂ n f (physicalComplexCoordinatesCLM x)‖ := by
  apply (iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesCLM) x).opNorm_le_bound
    (norm_nonneg _)
  intro v
  rw [physical_iteratedFDeriv_complex_restriction hf n v]
  calc
    _ ≤ ‖iteratedFDeriv ℂ n f (physicalComplexCoordinatesCLM x)‖ *
        ∏ i, ‖physicalComplexCoordinatesCLM (v i)‖ :=
      (iteratedFDeriv ℂ n f (physicalComplexCoordinatesCLM x)).le_opNorm _
    _ ≤ ‖iteratedFDeriv ℂ n f (physicalComplexCoordinatesCLM x)‖ * ∏ i, ‖v i‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => physicalComplexCoordinatesCLM_apply_norm_le _)

theorem physical_centered_iteratedFDeriv_complex_restriction
    (t0 : Position) {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesAt t0 x))
    (n : ℕ) (v : Fin n → Position × Position) :
    iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesAt t0) x v =
      iteratedFDeriv ℂ n f (physicalComplexCoordinatesAt t0 x)
        (fun i => physicalComplexCoordinatesCLM (v i)) := by
  have he : f ∘ physicalComplexCoordinatesAt t0 =
      fun q => (f ∘ physicalComplexCoordinatesCLM) (q-((0:Position),t0)) := by
    funext q
    have hq : q-((0:Position),t0)=(q.1,q.2-t0) := by apply Prod.ext <;> simp
    simp only [Function.comp_apply,physicalComplexCoordinatesAt,hq]
  rw [he,iteratedFDeriv_comp_sub n ((0:Position),t0) x]
  have hx : physicalComplexCoordinatesCLM (x-((0:Position),t0))=physicalComplexCoordinatesAt t0 x := by
    dsimp only [physicalComplexCoordinatesAt]
    congr 1
    apply Prod.ext <;> simp
  rw [← hx] at hf ⊢
  exact physical_iteratedFDeriv_complex_restriction hf n v

theorem physical_centered_iteratedFDeriv_norm_le_complex
    (t0 : Position) {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesAt t0 x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesAt t0) x‖ ≤
      ‖iteratedFDeriv ℂ n f (physicalComplexCoordinatesAt t0 x)‖ := by
  have he : f ∘ physicalComplexCoordinatesAt t0 =
      fun q => (f ∘ physicalComplexCoordinatesCLM) (q-((0:Position),t0)) := by
    funext q
    have hq : q-((0:Position),t0)=(q.1,q.2-t0) := by apply Prod.ext <;> simp
    simp only [Function.comp_apply,physicalComplexCoordinatesAt,hq]
  rw [he,iteratedFDeriv_comp_sub n ((0:Position),t0) x]
  have hx : physicalComplexCoordinatesCLM (x-((0:Position),t0))=physicalComplexCoordinatesAt t0 x := by
    dsimp only [physicalComplexCoordinatesAt]
    congr 1
    apply Prod.ext <;> simp
  rw [← hx] at hf ⊢
  exact physical_iteratedFDeriv_norm_le_complex hf n

#print axioms physical_iteratedFDeriv_complex_restriction
#print axioms physical_iteratedFDeriv_norm_le_complex
#print axioms physical_centered_iteratedFDeriv_complex_restriction
#print axioms physical_centered_iteratedFDeriv_norm_le_complex

def physicalCoordinateDirection : Fin 3 ⊕ Fin 3 → Position × Position :=
  Sum.elim (fun i => (PiLp.single 2 i (1:ℝ),0)) (fun i => (0,PiLp.single 2 i (1:ℝ)))

theorem physicalCoordinateDirection_norm (i : Fin 3 ⊕ Fin 3) :
    ‖physicalCoordinateDirection i‖=1 := by
  cases i <;> simp [physicalCoordinateDirection,Prod.norm_def,PiLp.norm_single]

theorem physicalComplexCoordinatesCLM_coordinateDirection (i : Fin 3 ⊕ Fin 3) :
    physicalComplexCoordinatesCLM (physicalCoordinateDirection i)=Pi.single i (1:ℂ) := by
  cases i with
  | inl j => exact physicalComplexCoordinatesCLM_x_basis j
  | inr j => exact physicalComplexCoordinatesCLM_t_basis j

theorem physical_centered_iteratedFDeriv_coordinate_word
    (t0 : Position) {f : (Fin 3 ⊕ Fin 3 → ℂ) → ℂ} {x : Position × Position}
    (hf : AnalyticAt ℂ f (physicalComplexCoordinatesAt t0 x))
    (n : ℕ) (w : Fin n → Fin 3 ⊕ Fin 3) :
    iteratedFDeriv ℝ n (f ∘ physicalComplexCoordinatesAt t0) x
      (fun i => physicalCoordinateDirection (w i)) =
      iteratedFDeriv ℂ n f (physicalComplexCoordinatesAt t0 x)
        (fun i => Pi.single (w i) (1:ℂ)) := by
  rw [physical_centered_iteratedFDeriv_complex_restriction t0 hf n]
  congr 1
  funext i
  exact physicalComplexCoordinatesCLM_coordinateDirection (w i)

#print axioms physicalCoordinateDirection_norm
#print axioms physical_centered_iteratedFDeriv_coordinate_word
end ManyBody.S8